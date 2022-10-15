SELECT
	StudentId,
	StudentName,
	GroupName
FROM Students, Groups
WHERE Students.StudentId NOT IN (
      SELECT DISTINCT Marks.StudentId FROM Marks
      WHERE Marks.CourseId = :CourseId
)
      AND Students.GroupId = Groups.GroupId;
