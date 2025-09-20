// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.9;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract VotingToken is ERC20 {
    constructor() ERC20("VotingToken", "VOTE") {
	_mint(msg.sender, 100 * 10**6);
    }

    function decimals() public view override returns (uint8) {
	return 6;
    }
}
