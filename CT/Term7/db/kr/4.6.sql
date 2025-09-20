SELECT
    TeamName,
    Solved
FROM
    Teams
    JOIN (
        SELECT
            TeamId,
            COUNT(DISTINCT Letter) AS Solved
        FROM
            Runs
            NATURAL JOIN Sessions
        WHERE
            Sessions.ContestId = :ContestId
            AND Runs.Accepted = 1
        GROUP BY
            TeamId) sq ON sq.TeamId = Teams.TeamId
    JOIN (
        SELECT
            TeamId,
            MIN(START) AS FirstStart
        FROM
            Sessions
        WHERE
            Sessions.ContestId = :ContestId
        GROUP BY
            TeamId) sqs ON sqs.TeamId = Teams.TeamId
ORDER BY
    Solved,
    FirstStart DESC;

