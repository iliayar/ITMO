SELECT SessionId, COUNT(DISTINCT Letter) AS Solved
FROM Sessions
     NATURAL LEFT JOIN Runs
     WHERE Accepted = 1
GROUP BY SessionId;
