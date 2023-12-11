SELECT
    ProblemName
FROM (
    SELECT
        ContestId,
        Letter
    FROM
        Problems
    EXCEPT
    SELECT
        ContestId,
        Letter
    FROM
        Sessions
    NATURAL JOIN Runs
WHERE
    Runs.Accepted = 1) sq
JOIN Problems ON sq.ContestId = Problems.ContestId
    AND sq.Letter = Problems.Letter;

