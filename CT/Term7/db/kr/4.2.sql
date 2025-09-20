SELECT
    TeamId,
    SUM(Opened) AS Opened
FROM (
    SELECT
        TeamId,
        ContestId,
        COUNT(DISTINCT Letter) AS Opened
    FROM
        Runs
    NATURAL JOIN Sessions
GROUP BY
    TeamId,
    ContestId) sq
GROUP BY TeamId;

