DELETE FROM Runs
WHERE SessionId IN (
      SELECT SessionId
      FROM Sessions
      WHERE TeamId = :TeamId
);
