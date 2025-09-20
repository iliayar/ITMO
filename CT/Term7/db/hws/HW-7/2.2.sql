UPDATE Students
SET GroupId = :GroupId
WHERE StudentId = :StudentId
      AND GroupId = :FromGroupId;
