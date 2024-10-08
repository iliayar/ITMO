DELETE FROM Runs
WHERE SessionId IN (
        SELECT
            SessionId
        FROM
            Sessions
        NATURAL JOIN Contests
    WHERE
        ContestName = :ContestName);

