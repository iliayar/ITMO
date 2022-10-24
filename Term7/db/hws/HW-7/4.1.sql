INSERT INTO Marks
       SELECT StudentId, CourseId, Mark
       FROM NewMarks
       WHERE NOT EXISTS (
       	     SELECT * FROM Marks
	     WHERE Marks.StudentId = NewMarks.StudentId
	     	   AND Marks.CourseId = NewMarks.CourseId
       );
