SELECT DISTINCT
	Students.StudentId,
	Students.StudentName,
	Groups.GroupName
FROM Students, Groups, Plan
WHERE Students.GroupId = Groups.GroupId
      AND Students.GroupId = Plan.GroupId
      AND Plan.CourseId IN (
      	  SELECT Courses.CourseId
	  FROM Courses
	  WHERE Courses.CourseName = :CourseName
      )
      AND Students.StudentId NOT IN (
      	  SELECT DISTINCT Marks.StudentId FROM Marks
      	  WHERE Marks.CourseId IN (
	  	SELECT Courses.CourseID
		FROM Courses
		WHERE Courses.CourseName = :CourseName
	  )
      );
