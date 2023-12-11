SELECT
    RunId,
    SessionId,
    Letter,
    SubmitTime
FROM
    Sessions
    NATURAL JOIN Runs
WHERE
    Accepted = 0
    AND ContestId = :ContestId;

