SELECT DISTINCT TeamName
FROM Teams
     NATURAL JOIN Sessions
     NATURAL JOIN Runs
WHERE ContestId = :ContestId
      AND Letter = :Letter
      AND Accepted = 1;
