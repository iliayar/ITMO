# Solidity, typical patterns
## Instruction
Install deps with:
```shell
npm install
```

Run test with:
```shell
npx hardhat test
```

## Example
```shell
  Requirements
    ✔ Decimals is 6 (1061ms)
    ✔ Owner has (70ms)
    ✔ Can create voting contract (88ms)
    ✔ Can create proposal (92ms)
    ✔ Accept/Reject proposal 1 (132ms)
    ✔ Accept/Reject proposal 2 (140ms)
    ✔ Accept/Reject proposal 3 (146ms)
    ✔ Should has not more than 3 active proposals (117ms)
    ✔ Most obsolete should have been discarded after TTL exceeded (158ms)
    ✔ Can vote for two proposals simultaniously (175ms)

  Reverts
    ✔ Can vote only once (110ms)
    ✔ Can create only unique proposal (84ms)
    ✔ Cannot access missing proposal (119ms)
    ✔ Cannot with zero amount of votes (83ms)
    ✔ Cannot vote for inactive proposal (139ms)
    ✔ Balance of tokens should be greater than votes (81ms)

  Views
    ✔ Get deadline/votesFor/votesAgainst (125ms)

  Extra
    ✔ Discraded when met invalid tokens balance (113ms)


  18 passing (3s)
```
