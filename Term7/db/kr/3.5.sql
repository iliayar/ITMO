UPDATE
    Runs
SET
    Accepted = 0
WHERE
    Runs.RunId IN (
        SELECT
            Runs.RunId
        FROM (
            SELECT
                SessionId,
                Letter,
                MIN(SubmitTime) AS SubmitTime
            FROM
                Runs
            GROUP BY
                SessionId,
                Letter) sq
            JOIN Runs ON sq.SessionId = Runs.SessionId
                AND sq.SubmitTime = Runs.SubmitTime
                AND sq.Letter = Runs.Letter);

