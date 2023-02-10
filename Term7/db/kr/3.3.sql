INSERT INTO Sessions(TeamId, ContestId, Start)
SELECT TeamId, :ContestId AS ContestId, CURRENT_TIMESTAMP AS START
FROM Teams
WHERE TeamId NOT IN (
      SELECT TeamId
      FROM Sessions
      WHERE ContestId = :ContestId
);
