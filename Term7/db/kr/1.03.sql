SELECT RunId, SessionId, Letter, SubmitTime
FROM Sessions
     NATURAL JOIN Runs
WHERE Accepted = 1
      AND ContestId = :ContestId;
