SELECT StudentId, StudentName, GroupId
FROM Students
WHERE GroupId IN (
      SELECT Groups.GroupId
      FROM Groups
      WHERE GroupName = :GroupName
);
