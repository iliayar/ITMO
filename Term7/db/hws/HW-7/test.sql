SELECT *
FROM Students
JOIN Marks ON Students.StudentId = Marks.StudentId
LEFT JOIN Plan ON Students.GroupId = Plan.GroupId
AND Marks.CourseId = Plan.CourseId;
