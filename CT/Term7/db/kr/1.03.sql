SELECT
    RunId,
    TeamId,
    SubmitTime,
    Accepted
FROM
    Sessions
    NATURAL JOIN Runs
WHERE
    Letter = :Letter
    AND ContestId = :ContestId;

