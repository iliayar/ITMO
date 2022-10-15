SELECT
	StudentId,
	StudentName,
	GroupName
FROM Students, Groups
WHERE Groups.GroupId = Students.GroupId;
