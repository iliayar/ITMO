// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract AmogusCoin is ERC20 {
    constructor() ERC20("AmogusCount", "AMOGUS") {
	_mint(msg.sender, 54 * 10**18);
    }
}
