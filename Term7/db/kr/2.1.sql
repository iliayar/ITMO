SELECT DISTINCT TeamId
FROM Sessions
     NATURAL JOIN Runs
WHERE ContestId = :ContestId
      AND Letter = :Letter
      AND Accepted = 1;
