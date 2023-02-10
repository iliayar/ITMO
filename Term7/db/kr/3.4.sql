UPDATE Runs
SET Accepted = 1
WHERE Runs.RunId IN (
      SELECT R.RunId
      FROM Runs AS R
      WHERE R.SessionId = Runs.SessionId
      ORDER BY R.SubmitTime DESC
      LIMIT 1
);
