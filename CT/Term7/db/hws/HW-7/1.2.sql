DELETE FROM Students
WHERE GroupId IN (
      SELECT GroupId
      FROM Groups
      Where GroupName = :GroupName
);
