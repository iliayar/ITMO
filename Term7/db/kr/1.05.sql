SELECT
    ProblemName
FROM (
    SELECT
        Letter,
        ContestId
    FROM
        Problems
    EXCEPT
    SELECT
        Letter,
        ContestId
    FROM
        Runs
    NATURAL JOIN Sessions
WHERE
    Accepted = 1) sq
JOIN Problems ON sq.Letter = Problems.Letter
    AND sq.ContestId = Problems.ContestId;

