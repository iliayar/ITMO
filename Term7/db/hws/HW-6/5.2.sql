SELECT StudentId
FROM Students
WHERE Students.StudentId NOT IN (
      SELECT Marks.StudentId
      FROM Marks
      WHERE Marks.CourseId IN (
      	    SELECT Plan.CourseId
	    FROM Plan, Lecturers
	    WHERE Plan.LecturerId = Lecturers.LecturerId
	    	  AND Lecturers.LecturerName = :LecturerName
		  AND Plan.GroupId = Students.GroupId
      )
);
