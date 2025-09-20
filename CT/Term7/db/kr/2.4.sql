SELECT
    ContestId,
    Letter
FROM
    Problems
EXCEPT
SELECT
    ContestId,
    Letter
FROM (
    SELECT
        SessionId,
        ContestId,
        Letter
    FROM
        Problems
    NATURAL JOIN Sessions
EXCEPT
SELECT
    SessionId,
    ContestId,
    Letter
FROM
    Runs
    NATURAL JOIN Sessions
WHERE
    Runs.Accepted = 1) sq;

