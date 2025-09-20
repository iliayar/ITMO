SELECT
    TeamName
FROM ( SELECT DISTINCT
        TeamId
    FROM
        Sessions
    WHERE
        ContestId = :ContestId) sq
    NATURAL JOIN Teams;

