-- TODO
SELECT
    sqq.Letter
FROM (
    SELECT
        MIN(Solved) AS MinSolved
    FROM (
        SELECT
            Letter,
            COUNT(DISTINCT SessionId) AS Solved
        FROM
            Runs
        NATURAL JOIN Sessions
    WHERE
        Sessions.ContestId = :ContestId
        AND Runs.Accepted = 1
    GROUP BY
        Letter) ssq) sq
    JOIN (
        SELECT
            Letter,
            COUNT(DISTINCT SessionId) AS Solved
        FROM
            Runs
            NATURAL JOIN Sessions
        WHERE
            Sessions.ContestId = :ContestId
            AND Runs.Accepted = 1
        GROUP BY
            Letter) sqq ON sqq.Solved = sq.MinSolved;

