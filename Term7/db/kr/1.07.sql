SELECT
    TeamName
FROM (
    SELECT
        TeamName,
        TeamId
    FROM
        Teams
    EXCEPT
    SELECT
        TeamName,
        TeamId
    FROM
        Runs
    NATURAL JOIN Sessions
    NATURAL JOIN Teams) sq;

