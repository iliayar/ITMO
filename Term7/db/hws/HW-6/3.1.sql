SELECT StudentId, CourseId
FROM Students, Plan
WHERE Students.GroupId = Plan.GroupId

UNION

SELECT StudentId, CourseId
FROM Marks;
