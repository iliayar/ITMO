SELECT StudentId, StudentName, GroupId
FROM Students
WHERE StudentId IN (
      SELECT Marks.StudentId
      FROM Marks
      WHERE Marks.CourseId IN (
      	    SELECT Courses.CourseId
	    FROM Courses
	    WHERE Courses.CourseName = :CourseName
      )
	    AND Marks.Mark = :Mark
);
