INSERT INTO Runs (SessionId, Letter, SubmitTime, Accepted)
SELECT
    SessionId,
    Letter,
    MAX(SubmitTime) + 1 AS SubmitTime,
    1 AS Accepted
FROM
    Runs
    NATURAL JOIN Sessions
WHERE
    NOT EXISTS (
        SELECT
            *
        FROM
            Runs AS R
        WHERE
            Runs.SessionId = R.SessionId
            AND Runs.Letter = R.Letter
            AND R.Accepted = 1)
    AND Sessions.ContestId = :ContestId
GROUP BY
    Runs.SessionId,
    Letter;

