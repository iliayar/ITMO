SELECT
    sqq.Letter
FROM (
    SELECT
        ContestId,
        MAX(Solved) AS MaxSolved
    FROM (
        SELECT
            ContestId,
            Letter,
            COUNT(DISTINCT SessionId) AS Solved
        FROM
            Runs
        NATURAL JOIN Sessions
    WHERE
        Runs.Accepted = 1
    GROUP BY
        ContestId,
        Letter) ssq
GROUP BY
    ContestId) sq
    JOIN (
        SELECT
            ContestId,
            Letter,
            COUNT(DISTINCT SessionId) AS Solved
        FROM
            Runs
            NATURAL JOIN Sessions
        WHERE
            Runs.Accepted = 1
        GROUP BY
            ContestId,
            Letter) sqq ON sqq.Solved = sq.MaxSolved
    AND sqq.ContestId = sq.ContestId;

