SELECT StudentName, CourseName
FROM (
     SELECT DISTINCT StudentId, CourseId
     FROM Students, Plan
     WHERE Students.GroupId = Plan.GroupId
     	   AND Students.StudentId NOT IN (
	       SELECT DISTINCT StudentId
	       FROM Marks
	       WHERE Marks.CourseId = Plan.CourseId
	   )
) AS SC, Students, Courses
WHERE SC.StudentId = Students.StudentId
      AND SC.CourseId = Courses.CourseId;
