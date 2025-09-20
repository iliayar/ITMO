// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.9;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract Voting {

    event Discarded(uint256 id);
    event Accepted(uint256 id);
    event Rejected(uint256 id);

    struct Vote {
	address from;
	uint256 amount;
    }

    struct Proposal {
	uint256 id;
	bool active;
	uint256 deadline;

	Vote[] votesFor;
	Vote[] votesAgainst;
    }
	
    uint constant PROPOSALS_COUNT = 3;
    uint constant PROPOSAL_TTL = 3 * 24 * 60 * 60;

    ERC20 immutable token; 

    Proposal[PROPOSALS_COUNT] proposals;

    constructor(ERC20 _token) {
	token = _token;

	for (uint i = 0; i < PROPOSALS_COUNT; i++) {
	    proposals[i].active = false;
	}
    }

    /// Create a proposal
    /// @param id Identifier of proposal
    function createProposal(uint256 id) public {
	uint idx = _findFreeIdx();
	require(idx != PROPOSALS_COUNT, "No free slots for new proposal");
	require(_findProposalIndex(id) == PROPOSALS_COUNT, "Such proposal already exists");

	if (!proposals[idx].active) {
	    proposals[idx].active = true;
	} else {
	    emit Discarded(proposals[idx].id);
	}

	proposals[idx].id = id;
	proposals[idx].deadline = block.timestamp + PROPOSAL_TTL;
	delete proposals[idx].votesFor;
	delete proposals[idx].votesAgainst;
    }

    /// Vote agains proposal
    /// @param id Identifier of proposal
    /// @param amount Amount of votes
    function voteFor(uint256 id, uint256 amount) public {
	uint idx = _getProposalIndexValidate(id, amount);
	if (!_checkProposalVotesValid(idx)) {
	    proposals[idx].active = false;
	    emit Discarded(id);
	    return;
	}

	proposals[idx].votesFor.push(Vote(msg.sender, amount));
	proposals[idx].active = !_checkCompleted(idx);
    }

    /// Vote agains proposal
    /// @param id Identifier of proposal
    /// @param amount Amount of votes
    function voteAgainst(uint256 id, uint256 amount) public {
	uint idx = _getProposalIndexValidate(id, amount);
	if (!_checkProposalVotesValid(idx)) {
	    proposals[idx].active = false;
	    emit Discarded(id);
	    return;
	}

	proposals[idx].votesAgainst.push(Vote(msg.sender, amount));
	proposals[idx].active = !_checkCompleted(idx);
    }

    /// Get proposal expiration date
    /// @param id Identifier of proposal
    /// @return Expiration date
    function getDeadline(uint256 id) public view returns (uint256) {
	uint idx = _findProposalIndex(id);
	require(idx != PROPOSALS_COUNT, "No such proposal");

	return proposals[idx].deadline;
    }

    /// Get total votes for proposal
    /// @param id Identifier of proposal
    /// @return Total votes
    function getVotesFor(uint256 id) public view returns (uint256) {
	uint idx = _findProposalIndex(id);
	require(idx != PROPOSALS_COUNT, "No such proposal");

	return _countVotes(proposals[idx].votesFor);
    }

    /// Get total votes against proposal
    /// @param id Identifier of proposal
    /// @return Total votes
    function getVotesAgainst(uint256 id) public view returns (uint256) {
	uint idx = _findProposalIndex(id);
	require(idx != PROPOSALS_COUNT, "No such proposal");

	return _countVotes(proposals[idx].votesAgainst);
    }

    /// Checks proposal is active
    /// @param id Identifier of proposal
    /// @return True if active, false otherwise
    function checkActive(uint256 id) public view returns (bool) {
	uint idx = _findProposalIndex(id);

	if (idx == PROPOSALS_COUNT) return false;

	return proposals[idx].active;
    }

    /// Check is proposal has free slots
    /// @return True if has, false otherwise
    function hasFreeSlots() public view returns (bool) {
	uint idx = _findFreeIdx();
	return idx != PROPOSALS_COUNT;
    }

    /// Helper for validate params
    /// @param id Identifier of proposal
    /// @param amount Amount of votes
    /// @return Index of proposal
    function _getProposalIndexValidate(uint256 id, uint256 amount) internal view returns (uint) {
	require(amount > 0, "Votes should be positive number");

	uint idx = _findProposalIndex(id);
	require(idx != PROPOSALS_COUNT, "No such proposal");
	require(proposals[idx].active, "Proposal is inactive");
	require(token.balanceOf(msg.sender) >= amount, "Not enough tokens for vote");
	require(_checkAlreadyVoted(msg.sender, idx), "Already voted for proposal");

	return idx;
    }


    /// Searches for a proposal by id
    /// @param id Idefntifier of proposal
    /// @return Index of proposal. If no, returns PROPOSALS_COUNT
    function _findProposalIndex(uint256 id) internal view returns (uint) {
	for (uint i = 0; i < PROPOSALS_COUNT; i++) {
	    if (proposals[i].id == id) return i;
	}
	return PROPOSALS_COUNT;
    }


    /// Searches for free proposal slot. If no, searches for expired
    /// most obsolete one.
    /// @return Index of free proposal slot or PROPOSALS_COUNT if none was found
    function _findFreeIdx() internal view returns (uint) {
	for (uint i = 0; i < PROPOSALS_COUNT; i++) {
	    if (!proposals[i].active) return i;
	}

	uint256 min_deadline = block.timestamp;
	uint min_idx = PROPOSALS_COUNT;
	for (uint i = 0; i < PROPOSALS_COUNT; i++) {
	    if (proposals[i].deadline < min_deadline) {
		min_deadline = proposals[i].deadline;
		min_idx = i;
	    }
	}

	return min_idx;
    }

    /// Checks if the proposal in completed with any result or not
    /// @param idx The index of proposal
    /// @return True if completed, false otherwise
    function _checkCompleted(uint idx) internal returns (bool) {
	if (_countVotes(proposals[idx].votesFor) >= 50) {
	    emit Accepted(proposals[idx].id);
	    return true;
	}

	if (_countVotes(proposals[idx].votesAgainst) >= 50) {
	    emit Rejected(proposals[idx].id);
	    return true;
	}

	return false;
    }

    /// Count total amount of voutes. Takes a weigth of vote is
    /// equals to maximum of user has and the mount given to proposal
    /// @param votes Array of votes. Either votesFor or votesAgains
    /// @return Total amount of votes
    function _countVotes(Vote[] storage votes) internal view returns (uint256) {
	uint256 total = 0;
	for (uint i = 0; i < votes.length; ++i) {
	    total += votes[i].amount;
	}

	return total;
    }

    /// Checks either any user votes, has invalud amount of tokens
    /// @param idx Index of proposal
    /// @return True if all votes are valid, false otherwise
    function _checkProposalVotesValid(uint idx) internal view returns (bool) {
	return _checkVotesValid(proposals[idx].votesFor)
	    && _checkVotesValid(proposals[idx].votesAgainst);
    }

    /// Checks either any user votes, has invalud amount of tokens
    /// @param votes Array of votes. Either votesFor or votesAgains
    /// @return True if all votes are valid, false otherwise
    function _checkVotesValid(Vote[] storage votes) internal view returns (bool) {
	for (uint i = 0; i < votes.length; ++i) {
	    if (token.balanceOf(votes[i].from) < votes[i].amount) {
		return false;
	    }
	}

	return true;
    }

    /// Checks user already voted
    /// @param user The user
    /// @param idx Index of proposal
    /// @return True if no votes, false, otherwise
    function _checkAlreadyVoted(address user, uint idx) internal view returns (bool) {
	return _checkAlreadyVoted(user, proposals[idx].votesFor)
	    && _checkAlreadyVoted(user, proposals[idx].votesAgainst);
    }

    /// Checks user already voted
    /// @param user The user
    /// @param votes Array of votes. Either votesFor or votesAgains
    /// @return True if no votes, false, otherwise
    function _checkAlreadyVoted(address user, Vote[] storage votes) internal view returns (bool) {
	for (uint i = 0; i < votes.length; ++i) {
	    if (votes[i].from == user) {
		return false;
	    }
	}

	return true;
    }
}
