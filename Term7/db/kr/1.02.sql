SELECT RunId, SessionId, Letter, SubmitTime, Accepted
FROM Sessions
     NATURAL JOIN Runs
WHERE TeamId = :TeamId
      AND ContestId = :ContestId;
