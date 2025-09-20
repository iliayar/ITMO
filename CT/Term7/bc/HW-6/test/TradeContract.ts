import { expect } from "chai";
import { ethers } from "hardhat";

describe("Trade Contract", function () {
  it("Test transfer", async function () {
    // Random address with a bunch of WETH
    const WETH_USER = "0x7ceB23fD6bC0adD59E62ac25578270cFf1b9f619";
    const owner = await ethers.getImpersonatedSigner(WETH_USER);
    const balance = ethers.utils.parseEther("0.001");
    const flashloanAmount = ethers.utils.parseEther("0.005");

    const LendingPoolAddressProviderAddress = "0xB53C1a33016B2DC2fF3653530bfF1848a515c8c5";
    const WETHAddress = "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2";

    const Flashloan = await ethers.getContractFactory("Flashloan");
    const flashloan = await Flashloan.deploy(LendingPoolAddressProviderAddress, flashloanAmount);
    await flashloan.deployed()

    const WETH = await ethers.getContractAt("IERC20", WETHAddress);

    const prevBalance = await WETH.balanceOf(owner.address)
    expect(prevBalance).to.greaterThan(balance);
    await WETH.connect(owner).transfer(flashloan.address, balance)

    expect(await WETH.balanceOf(owner.address)).to.equal(prevBalance.sub(balance));
    expect(await WETH.balanceOf(flashloan.address)).to.equal(balance);

    await expect(flashloan.flashloan())
      .to.emit(flashloan, "LogBalances")
      .withArgs(
	  balance.add(flashloanAmount),
	  ethers.BigNumber.from("830831382461664813"),
	  ethers.BigNumber.from("5830345"),
      );

    expect(await WETH.balanceOf(flashloan.address))
      .to.lessThan(balance)
      .and.greaterThan(0);
  })
});
