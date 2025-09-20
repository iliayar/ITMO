// Copyright (C) 2018  MixBytes, LLC

// Licensed under the Apache License, Version 2.0 (the "License").
// You may not use this file except in compliance with the License.

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND (express or implied).

pragma solidity ^0.4.24;

import 'openzeppelin-solidity/contracts/token/ERC20/StandardToken.sol';

import 'openzeppelin-solidity/contracts/ownership/Ownable.sol';


contract DividendToken is StandardToken, Ownable {
    event PayDividend(address indexed to, uint256 amount);
    event HangingDividend(address indexed to, uint256 amount) ;
    event PayHangingDividend(uint256 amount) ;
    event Deposit(address indexed sender, uint256 value);

    /// @dev parameters of an extra token emission
    struct EmissionInfo {
        // new totalSupply after emission happened
        uint256 totalSupply;

        // total balance of Ether stored at the contract when emission happened
        uint256 totalBalanceWas;
    }

    constructor () public
    {
        m_emissions.push(EmissionInfo({
            totalSupply: totalSupply(),
            totalBalanceWas: 0
        }));
    }

    function() external payable {
        if (msg.value > 0) {
            emit Deposit(msg.sender, msg.value);
            m_totalDividends = m_totalDividends.add(msg.value);
        }
    }

    /// @notice Request dividends for current account.
    function requestDividends() public {
        payDividendsTo(msg.sender);
    }

    /// @notice Request hanging dividends to pwner.
    function requestHangingDividends() onlyOwner public {
        owner.transfer(m_totalHangingDividends);
        emit PayHangingDividend(m_totalHangingDividends);
        m_totalHangingDividends = 0;
    }

    /// @notice hook on standard ERC20#transfer to pay dividends
    function transfer(address _to, uint256 _value) public returns (bool) {
        payDividendsTo(msg.sender);
        payDividendsTo(_to);
        return super.transfer(_to, _value);
    }

    /// @notice hook on standard ERC20#transferFrom to pay dividends
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool) {
        payDividendsTo(_from);
        payDividendsTo(_to);
        return super.transferFrom(_from, _to, _value);
    }

    /// @dev adds dividends to the account _to
    function payDividendsTo(address _to) internal {
        (bool hasNewDividends, uint256 dividends, uint256 lastProcessedEmissionNum) = calculateDividendsFor(_to);
        if (!hasNewDividends)
            return;

        if (0 != dividends) {
            bool res = _to.send(dividends);
            if (res) {
                emit PayDividend(_to, dividends);
            }
            else{
                // _to probably is a contract not able to receive ether
                emit HangingDividend(_to, dividends);
                m_totalHangingDividends = m_totalHangingDividends.add(dividends);
            }
        }

        m_lastAccountEmission[_to] = lastProcessedEmissionNum;
        if (lastProcessedEmissionNum == getLastEmissionNum()) {
            m_lastDividents[_to] = m_totalDividends;
        }
        else {
            m_lastDividents[_to] = m_emissions[lastProcessedEmissionNum.add(1)].totalBalanceWas;
        }
    }

    /// @dev calculates dividends for the account _for
    /// @return (true if state has to be updated, dividend amount (could be 0!), lastProcessedEmissionNum)
    function calculateDividendsFor(address _for) view internal returns (
        bool hasNewDividends,
        uint256 dividends,
        uint256 lastProcessedEmissionNum
    ) {
        uint256 lastEmissionNum = getLastEmissionNum();
        uint256 lastAccountEmissionNum = m_lastAccountEmission[_for];
        assert(lastAccountEmissionNum <= lastEmissionNum);

        uint256 totalBalanceWasWhenLastPay = m_lastDividents[_for];

        assert(m_totalDividends >= totalBalanceWasWhenLastPay);

        // If no new ether was collected since last dividends claim
        if (m_totalDividends == totalBalanceWasWhenLastPay)
            return (false, 0, lastAccountEmissionNum);

        uint256 initialBalance = balances[_for];    // beware of recursion!

        // if no tokens owned by account
        if (0 == initialBalance)
            return (true, 0, lastEmissionNum);

        // We start with last processed emission because some ether could be collected before next emission
        // we pay all remaining ether collected and continue with all the next emissions
        uint256 iter = 0;
        uint256 iterMax = getMaxIterationsForRequestDividends();

        for (uint256 emissionToProcess = lastAccountEmissionNum; emissionToProcess <= lastEmissionNum; emissionToProcess++) {
            if (iter++ > iterMax)
                break;

            lastAccountEmissionNum = emissionToProcess;
            EmissionInfo storage emission = m_emissions[emissionToProcess];

            if (0 == emission.totalSupply)
                continue;

            uint256 totalEtherDuringEmission;
            // last emission we stopped on
            if (emissionToProcess == lastEmissionNum) {
                totalEtherDuringEmission = m_totalDividends.sub(totalBalanceWasWhenLastPay);
            }
            else {
                totalEtherDuringEmission = m_emissions[emissionToProcess.add(1)].totalBalanceWas.sub(totalBalanceWasWhenLastPay);
                totalBalanceWasWhenLastPay = m_emissions[emissionToProcess.add(1)].totalBalanceWas;
            }

            uint256 dividend = totalEtherDuringEmission.mul(initialBalance).div(emission.totalSupply);
            dividends = dividends.add(dividend);
        }

        return (true, dividends, lastAccountEmissionNum);
    }

    function getLastEmissionNum() private view returns (uint256) {
        return m_emissions.length - 1;
    }

    /// @dev to prevent gasLimit problems with many mintings
    function getMaxIterationsForRequestDividends() internal pure returns (uint256) {
        return 1000;
    }

    /// @notice record of issued dividend emissions
    EmissionInfo[] public m_emissions;

    /// @dev for each token holder: last emission (index in m_emissions) which was processed for this holder
    mapping(address => uint256) public m_lastAccountEmission;

    /// @dev for each token holder: last ether balance was when requested dividends
    mapping(address => uint256) public m_lastDividents;


    uint256 public m_totalHangingDividends;
    uint256 public m_totalDividends;
}
