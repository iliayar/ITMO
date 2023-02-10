// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.6.12;

import "@uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router02.sol";
import "@uniswap/v2-core/contracts/interfaces/IUniswapV2Factory.sol";
import "@aave/protocol-v2/contracts/flashloan/base/FlashLoanReceiverBase.sol";

interface PatchedERC20 {
    function approve(address to, uint256 amount) external;
    function balanceOf(address from) external view returns (uint256);
}

contract Flashloan is FlashLoanReceiverBase {
    event LogBalances(
	uint256 WETHBalance,
	uint256 LINKBalance,
	uint256 USDTBalance
    );

    PatchedERC20 constant WETH = PatchedERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    PatchedERC20 constant LINK = PatchedERC20(0x514910771AF9Ca656af840dff83E8264EcF986CA);
    PatchedERC20 constant USDT = PatchedERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);

    IUniswapV2Factory constant UNISWAP_FACTORY = IUniswapV2Factory(0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f);

    IUniswapV2Router02 constant ROUTER = IUniswapV2Router02(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);

    uint256 immutable FLASHLOAN_AMOUNT;

    constructor(ILendingPoolAddressesProvider _addressProvider, uint256 flashloanAmount) public FlashLoanReceiverBase(_addressProvider) {
	FLASHLOAN_AMOUNT = flashloanAmount;
    }

    function swap(PatchedERC20 tokenFrom, PatchedERC20 tokenTo, uint256 amount) private {
	address[] memory path = new address[](2);
	tokenFrom.approve(address(ROUTER), amount);
	path[0] = address(tokenFrom);
	path[1] = address(tokenTo);
	ROUTER.swapExactTokensForTokens(
	    amount,
	    0,
	    path,
	    address(this),
	    block.timestamp
	);
    }


    function swapAll(PatchedERC20 tokenFrom, PatchedERC20 tokenTo) private {
	uint256 amount = tokenFrom.balanceOf(address(this));
	swap(tokenFrom, tokenTo, amount);
    }

    function executeOperation(
	address[] calldata assets,
	uint256[] calldata amounts,
	uint256[] calldata premiums,
	address initiator,
	bytes calldata params
    )
	external
	override
	returns (bool)
    {
	uint256 WETHBalance = WETH.balanceOf(address(this));
	swap(WETH, LINK, amounts[0]);

	uint256 LINKBalance = LINK.balanceOf(address(this));
	swapAll(LINK, USDT);

	uint256 USDTBalance = USDT.balanceOf(address(this));
	swapAll(USDT, WETH);

	emit LogBalances(
	    WETHBalance,
	    LINKBalance,
	    USDTBalance
	);

	uint amountOwing = amounts[0].add(premiums[0]);
	IERC20(assets[0]).approve(address(LENDING_POOL), amountOwing);

	return true;
    }

    function flashloan() public {
	address receiverAddress = address(this);

	address[] memory assets = new address[](1);
	assets[0] = address(WETH);

	uint256[] memory amounts = new uint256[](1);
	amounts[0] = FLASHLOAN_AMOUNT;

	uint256[] memory modes = new uint256[](1);
	modes[0] = 0;

	address onBehalfOf = address(this);
	bytes memory params = "";
	uint16 referralCode = 0;

	LENDING_POOL.flashLoan(
	    receiverAddress,
	    assets,
	    amounts,
	    modes,
	    onBehalfOf,
	    params,
	    referralCode
	);
    }

}
