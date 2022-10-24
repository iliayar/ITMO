UPDATE Students
SET GroupId = (
    SELECT GroupId
    FROM Groups
    WHERE GroupName = :GroupName
)
WHERE GroupId IN (
      SELECT GroupId
      FROM Groups
      WHERE GroupName = :FromGroupName
)
      AND :GroupName IN (
      SELECT GroupName
      FROM Groups
);
