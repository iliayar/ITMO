SELECT
    SessionId,
    COUNT(DISTINCT Letter) AS Opened
FROM
    Runs
GROUP BY
    SessionId;

