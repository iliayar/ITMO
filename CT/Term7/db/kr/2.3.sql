SELECT DISTINCT TeamId
FROM Sessions
     NATURAL JOIN Runs
WHERE ContestId = :ContestId
      AND Accepted = 0;
