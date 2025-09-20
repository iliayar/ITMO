import { expect } from "chai";
import { ethers } from "hardhat";

describe("Token contract", function () {
	it("Deployment should assign the total suply of token to owner", async function () {
		const [owner] = await ethers.getSigners();

		const CringeCoin = await ethers.getContractFactory("CringeCoin");
		const cringeCoin = await CringeCoin.deploy();

		const ownerBalance = await cringeCoin.balanceOf(owner.address);
		expect(await cringeCoin.totalSupply()).to.equal(ownerBalance);
	});
	it("Should successfuly deploy uniswap contract and exchange tokens", async function () {
		const [owner] = await ethers.getSigners();

		const CringeCoin = await ethers.getContractFactory("CringeCoin");
		const cringeCoin = await CringeCoin.deploy();

		const AmogusCoin = await ethers.getContractFactory("AmogusCoin");
		const amogusCoin = await AmogusCoin.deploy();

		const uniswapFactoryAddress = "0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f";
		const uniswapRouterAddress = "0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D";

		const uniswapFactory = await ethers.getContractAt("IUniswapV2Factory", uniswapFactoryAddress);
		const uniswapRouter = await ethers.getContractAt("IUniswapV2Router02", uniswapRouterAddress);

		await uniswapFactory.createPair(amogusCoin.address, cringeCoin.address);

		await amogusCoin.approve(uniswapRouter.address, ethers.utils.parseEther("1"));
		await cringeCoin.approve(uniswapRouter.address, ethers.utils.parseEther("1"));

		await uniswapRouter.addLiquidity(amogusCoin.address, cringeCoin.address, ethers.utils.parseEther("1"), ethers.utils.parseEther("1"), 0, 0, owner.address, 1700165523);

		const amogusPrevBalance = await amogusCoin.balanceOf(owner.address);
		const cringePrevBalance = await cringeCoin.balanceOf(owner.address);

		await amogusCoin.approve(uniswapRouter.address, ethers.utils.parseEther("1"));
		await uniswapRouter.swapExactTokensForTokens(ethers.utils.parseEther("1"), 0, [amogusCoin.address, cringeCoin.address], owner.address, 1700165523)

		expect(await amogusCoin.balanceOf(owner.address)).to.be.lessThan(amogusPrevBalance);
		expect(await cringeCoin.balanceOf(owner.address)).to.be.greaterThan(cringePrevBalance);
	});
});
