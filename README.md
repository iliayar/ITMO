# Solidity + EVM, low-level patterns
## Instruction
Enter alchemy api key:
```shell
cat >> .env <<EOF
ALCHEMY_API_KEY=<API_KEY>
EOF
```

Install deps with:
```shell
npm install
```

Run test with:
```shell
npx hardhat test
```

## Example
```shell
  Token contract
    ✔ Deployment should assign the total suply of token to owner (2163ms)
    ✔ Should successfuly deploy uniswap contract and exchange tokens (261ms)


  2 passing (2s)
```
