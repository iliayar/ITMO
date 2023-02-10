DELETE FROM Runs
WHERE SessionId IN (
      SELECT SessionId
      FROM Sessions
      	   NATURAL JOIN Teams
      WHERE TeamName = :TeamName
);
