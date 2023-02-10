use std::str::FromStr;

use tokio;
use web3::{
    contract::{
        tokens::{Detokenize, Tokenizable},
        Contract, Options,
    },
    ethabi::Hash,
    futures::StreamExt,
    types::{BlockHeader, U256},
};

use log::*;

enum Rate {
    EthUsd,
    LinkEth,
    UsdtEth,
}

impl ToString for Rate {
    fn to_string(&self) -> String {
        match self {
            Rate::EthUsd => "ETH / USD",
            Rate::LinkEth => "LINK / ETH",
            Rate::UsdtEth => "USDT / ETH",
        }
        .to_string()
    }
}

struct FeedContract {
    addr: web3::types::Address,
    rate: Rate,
}

impl FeedContract {
    pub fn new(addr: impl AsRef<str>, rate: Rate) -> Self {
        return FeedContract {
            addr: web3::types::Address::from_str(addr.as_ref()).expect("Invalid address"),
            rate,
        };
    }
}

struct Monitor {
    web3: web3::Web3<web3::transports::WebSocket>,
    feeds: Vec<(Contract<web3::transports::WebSocket>, Rate)>,
}

struct LatestRoundData {
    round_id: U256,
    answer: U256,
    started_at: U256,
    updated_at: U256,
    answered_in_round: U256,
}

impl Detokenize for LatestRoundData {
    fn from_tokens(mut tokens: Vec<web3::ethabi::Token>) -> Result<Self, web3::contract::Error>
    where
        Self: Sized,
    {
        let mk_error = |msg: &str| web3::contract::Error::from(msg.to_string());
        if tokens.len() != 5 {
            Err(mk_error("Invalid len"))
        } else {
            let mut pop_checking = |field| {
                tokens
                    .pop()
                    .ok_or(mk_error(&format!("{} is missing", field)))
            };
            let answered_in_round_raw = pop_checking("answeredInRound")?;
            let updated_at_raw = pop_checking("updatedAt")?;
            let started_at_raw = pop_checking("startedAt")?;
            let answer_raw = pop_checking("answer")?;
            let round_id_raw = pop_checking("roundId")?;

            Ok(Self {
                round_id: round_id_raw
                    .into_uint()
                    .ok_or(mk_error("roundId is not uint"))?,
                answer: answer_raw.into_int().ok_or(mk_error("answer is not int"))?,
                started_at: started_at_raw
                    .into_uint()
                    .ok_or(mk_error("startedAt is not uint"))?,
                updated_at: updated_at_raw
                    .into_uint()
                    .ok_or(mk_error("updatedAt is not uint"))?,
                answered_in_round: answered_in_round_raw
                    .into_uint()
                    .ok_or(mk_error("answeredInRound is not uint"))?,
            })
        }
    }
}

impl Monitor {
    pub async fn new(api_key: impl AsRef<str>, feeds: Vec<FeedContract>) -> web3::Result<Self> {
        let transport = web3::transports::WebSocket::new(&format!(
            "wss://eth-mainnet.g.alchemy.com/v2/{}",
            api_key.as_ref(),
        ))
        .await?;
        let web3 = web3::Web3::new(transport);

        let mut contract_feeds = Vec::new();
        for feed in feeds.into_iter() {
            let contract =
                Contract::from_json(web3.eth(), feed.addr, include_bytes!("./res/abi.json"))
                    .expect("Failed to crate contract");

            contract_feeds.push((contract, feed.rate));
        }

        Ok(Self {
            web3,
            feeds: contract_feeds,
        })
    }

    pub async fn watch(&self) -> web3::Result {
        let mut block_subscription = self.web3.eth_subscribe().subscribe_new_heads().await?;

        while let Some(block) = block_subscription.next().await {
            if let Ok(block) = block {
                self.handle_new_block(block).await;
            } else {
                warn!("Called with no block");
            }
        }

        Ok(())
    }

    async fn handle_new_block(&self, block: BlockHeader) {
        info!("New block: {:?}", block.hash.expect("Block has no hash"));

        for (contract, rate) in self.feeds.iter() {
            let decimals = self.get_decimals(contract).await;
            let round_data = self.get_round_data(&contract).await;
            let mut price = round_data.answer;

            let mut float = Vec::<u8>::new();
            for _ in 0..decimals {
                let (new_price, digit) = price.div_mod(U256::from(10));
                float.push(b'0' + digit.as_u32() as u8);

                price = new_price;
            }
            float.reverse();

            info!(
                "{}: {}.{}",
                rate.to_string(),
                price,
                String::from_utf8(float).unwrap()
            );
        }
    }

    async fn get_round_data(
        &self,
        contract: &Contract<web3::transports::WebSocket>,
    ) -> LatestRoundData {
        self.view_contract("latestRoundData", contract)
            .await
            .unwrap()
    }

    async fn get_decimals(&self, contract: &Contract<web3::transports::WebSocket>) -> u8 {
        self.view_contract("decimals", contract).await.unwrap()
    }

    async fn view_contract<R: Detokenize>(
        &self,
        fun: &str,
        contract: &Contract<web3::transports::WebSocket>,
    ) -> web3::contract::Result<R> {
        contract
            .query(fun, (), None, Options::default(), None)
            .await
    }
}

#[tokio::main]
async fn main() -> web3::Result<()> {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );

    let feeds = vec![
        FeedContract::new("0x5f4eC3Df9cbd43714FE2740f5E3616155c5b8419", Rate::EthUsd),
        FeedContract::new("0xDC530D9457755926550b59e8ECcdaE7624181557", Rate::LinkEth),
        FeedContract::new("0xEe9F2375b4bdF6387aa8265dD4FB8F16512A1d46", Rate::UsdtEth),
    ];
    let mon = Monitor::new(env!("ALCHEMY_API_KEY"), feeds).await?;
    mon.watch().await?;

    Ok(())
}
