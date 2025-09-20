UPDATE
    Runs
SET
    Accepted = 1
WHERE
    Runs.RunId IN (
        SELECT
            Runs.RunId
        FROM (
            SELECT
                SessionId,
                MAX(SubmitTime) AS SubmitTime
            FROM
                Runs
            WHERE
                Accepted = 0
            GROUP BY
                SessionId) sq
            JOIN Runs ON sq.SessionId = Runs.SessionId
                AND sq.SubmitTime = Runs.SubmitTime);

