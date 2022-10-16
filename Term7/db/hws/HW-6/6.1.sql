SELECT GroupId, CourseId
From Groups AS G, Courses as C
WHERE NOT EXISTS (
      SELECT *
      FROM Students
      WHERE Students.GroupId = G.GroupId
      	    AND NOT EXISTS (
	    	SELECT *
		FROM Marks
		WHERE Marks.StudentId = Students.StudentId
		      AND Marks.CourseId = C.CourseId
	    )
);
