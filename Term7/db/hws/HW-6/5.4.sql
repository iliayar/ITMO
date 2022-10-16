SELECT StudentId
FROM Students AS S
WHERE NOT EXISTS (
      SELECT *
      FROM Lecturers, Plan
      WHERE Lecturers.LecturerName = :LecturerName
      	    AND Plan.LecturerId = Lecturers.LecturerId
	    AND Plan.GroupId = S.GroupId
	    AND NOT EXISTS (
      	    	SELECT *
	    	FROM Marks
	    	WHERE Marks.StudentId = S.StudentId
	    	      AND Marks.CourseId = Plan.CourseId
            )
);
