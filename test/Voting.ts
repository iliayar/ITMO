import { expect } from "chai";
import { ethers } from "hardhat";

import { time } from "@nomicfoundation/hardhat-network-helpers";

describe("Requirements", function () {
  it("Decimals is 6", async function () {
    const [owner] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    expect(await votingToken.decimals()).to.equal(6);
  });

  it("Owner has", async function () {
    const [owner] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    const ownerBalance = await votingToken.balanceOf(owner.address);
    const balance = ethers.BigNumber.from('100000000')
    expect(ownerBalance).to.equal(balance);
  });

  it("Can create voting contract", async function () {
    const [owner] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    expect(await voting.hasFreeSlots()).to.true;
  });

  it("Can create proposal", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);
    expect(await voting.checkActive(proposalId)).to.true;
  });

  it("Accept/Reject proposal 1", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 50);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);
    expect(await voting.connect(addr1).voteFor(proposalId, 50)).to
      .emit(voting, "Accepted")
      .withArgs(proposalId);
    expect(await voting.checkActive(proposalId)).to.false;
  });

  it("Accept/Reject proposal 2", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);
    await voting.connect(addr1).voteFor(proposalId, 30);
    expect(await voting.checkActive(proposalId)).to.true;
    expect(await voting.connect(addr2).voteFor(proposalId, 25)).to
      .emit(voting, "Accepted")
      .withArgs(proposalId);
    expect(await voting.checkActive(proposalId)).to.false;
  });

  it("Accept/Reject proposal 3", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);
    await voting.connect(addr1).voteFor(proposalId, 30);
    expect(await voting.checkActive(proposalId)).to.true;
    expect(await voting.connect(addr3).voteAgainst(proposalId, 60)).to
      .emit(voting, "Rejected")
      .withArgs(proposalId);
    expect(await voting.checkActive(proposalId)).to.false;
  });

  it("Should has not more than 3 active proposals", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposal1Id = ethers.BigNumber.from(1);
    const proposal2Id = ethers.BigNumber.from(2);
    const proposal3Id = ethers.BigNumber.from(3);
    const proposal4Id = ethers.BigNumber.from(4);

    await voting.connect(addr1).createProposal(proposal1Id);
    await voting.connect(addr1).createProposal(proposal2Id);
    await voting.connect(addr1).createProposal(proposal3Id);

    expect(voting.connect(addr1).createProposal(proposal4Id)).to
      .revertedWith("No free slots for new proposal");
  });

  it("Most obsolete should have been discarded after TTL exceeded", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposal1Id = ethers.BigNumber.from(1);
    const proposal2Id = ethers.BigNumber.from(2);
    const proposal3Id = ethers.BigNumber.from(3);
    const proposal4Id = ethers.BigNumber.from(4);

    await voting.connect(addr1).createProposal(proposal1Id);

    await time.increase(1 * 24 * 60 * 60);

    await voting.connect(addr1).createProposal(proposal2Id);
    await voting.connect(addr1).createProposal(proposal3Id);

    await time.increase(2 * 24 * 60 * 60);

    expect(await voting.connect(addr1).createProposal(proposal4Id)).to.not.reverted;
    expect(await voting.checkActive(proposal1Id)).to.false;
    expect(await voting.checkActive(proposal2Id)).to.true;
    expect(await voting.checkActive(proposal3Id)).to.true;
    expect(await voting.checkActive(proposal4Id)).to.true;
  });

  it("Can vote for two proposals simultaniously", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposal1Id = ethers.BigNumber.from(1);
    const proposal2Id = ethers.BigNumber.from(2);

    await voting.connect(addr1).createProposal(proposal1Id);
    await voting.connect(addr1).createProposal(proposal2Id);

    await voting.connect(addr1).voteFor(proposal1Id, 30);
    await voting.connect(addr1).voteAgainst(proposal2Id, 30);

    expect(await voting.connect(addr2).voteAgainst(proposal2Id, 25)).to
      .emit(voting, "Rejected")
      .withArgs(proposal2Id);

    expect(await voting.connect(addr2).voteFor(proposal1Id, 25)).to
      .emit(voting, "Accepted")
      .withArgs(proposal1Id);
  });
});

describe("Reverts", function () {
  it("Can vote only once", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    await voting.connect(addr1).voteFor(proposalId, 30);
    expect(voting.connect(addr1).voteAgainst(proposalId, 30)).to
      .revertedWith("Already voted for proposal");
  });

  it("Can create only unique proposal", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);
    expect(voting.connect(addr1).createProposal(proposalId)).to
      .revertedWith("Such proposal already exists");
  });

  it("Cannot access missing proposal", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);
    const proposalIdMissing = ethers.BigNumber.from(2);

    await voting.connect(addr1).createProposal(proposalId);

    await voting.connect(addr1).voteFor(proposalId, 30);
    await voting.connect(addr2).voteAgainst(proposalId, 25);

    expect(voting.connect(addr2).getDeadline(proposalIdMissing)).to
      .revertedWith("No such proposal")

    expect(voting.connect(addr2).getVotesAgainst(proposalIdMissing)).to
      .revertedWith("No such proposal")

    expect(voting.connect(addr2).getVotesFor(proposalIdMissing)).to
      .revertedWith("No such proposal")

    expect(voting.connect(addr2).voteFor(proposalIdMissing, 10)).to
      .revertedWith("No such proposal")
  });

  it("Cannot with zero amount of votes", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    expect(voting.connect(addr1).voteFor(proposalId, 0)).to
      .revertedWith("Votes should be positive number");
  });

  it("Cannot vote for inactive proposal", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    expect(await voting.connect(addr3).voteFor(proposalId, 50)).to
      .emit(voting, 'Accepted')
      .withArgs(proposalId);

    expect(voting.connect(addr2).voteAgainst(proposalId, 10)).to
      .revertedWith("Proposal is inactive");
  });
  it("Balance of tokens should be greater than votes", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    expect(voting.connect(addr3).voteFor(proposalId, 100)).to
      .revertedWith("Not enough tokens for vote");
  });
});

describe("Views", function () {
  it("Get deadline/votesFor/votesAgainst", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    await voting.connect(addr1).voteFor(proposalId, 30);
    await voting.connect(addr2).voteAgainst(proposalId, 25);

    expect(await voting.connect(addr2).getDeadline(proposalId)).to
      .equal(await time.latest() + 3 * 24 * 60 * 60 - 2);

    expect(await voting.connect(addr2).getVotesFor(proposalId)).to
      .equal(30);

    expect(await voting.connect(addr2).getVotesAgainst(proposalId)).to
      .equal(25);
  });
});

describe("Extra", function () {
  it("Discraded when met invalid tokens balance", async function () {
    const [owner, addr1, addr2, addr3] = await ethers.getSigners();

    const VotingToken = await ethers.getContractFactory("VotingToken");
    const votingToken = await VotingToken.deploy();

    votingToken.transfer(addr1.address, 30);
    votingToken.transfer(addr2.address, 25);
    votingToken.transfer(addr3.address, 70);

    const Voting = await ethers.getContractFactory("Voting");
    const voting = await Voting.deploy(votingToken.address);

    const proposalId = ethers.BigNumber.from(1);

    await voting.connect(addr1).createProposal(proposalId);

    await voting.connect(addr1).voteFor(proposalId, 30);
    await votingToken.connect(addr1).transfer(addr2.address, 25);

    expect(await voting.connect(addr2).voteAgainst(proposalId, 50)).to
      .emit(voting, 'Discarded')
      .withArgs(proposalId);

    expect(await voting.connect(addr2).checkActive(proposalId)).to.false;
  });
});
