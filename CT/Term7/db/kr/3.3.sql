INSERT INTO Sessions (TeamId, ContestId, START)
SELECT
    TeamId,
    :ContestId AS ContestId,
    CURRENT_TIMESTAMP AS START
FROM
    Sessions
WHERE
    ContestId = :ContestId;

