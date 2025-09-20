// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract CringeCoin is ERC20 {
    constructor() ERC20("CringeCoin", "CRINGE") {
	_mint(msg.sender, 1337 * 10**18);
    }
}
