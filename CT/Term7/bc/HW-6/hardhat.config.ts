import { HardhatUserConfig } from "hardhat/config";
import "@nomicfoundation/hardhat-toolbox";

require('dotenv').config()

const ALCHEMY_API_KEY = process.env.ALCHEMY_API_KEY;

if (!ALCHEMY_API_KEY) throw new Error("ALCHEMY_API_KEY required");

const config: HardhatUserConfig = {
    solidity: "0.6.12",
    defaultNetwork: "hardhat",
    networks: {
 	hardhat: {
 	    forking: {
		url: "https://eth-mainnet.alchemyapi.io/v2/" + ALCHEMY_API_KEY,
	      	blockNumber: 16093829,
	    },
 	},
    },
};

export default config;
