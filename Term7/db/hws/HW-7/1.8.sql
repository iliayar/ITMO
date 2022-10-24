DELETE FROM Students
WHERE StudentId IN (
      SELECT Students.StudentId
      FROM Students
      	   NATURAL JOIN Plan
	   LEFT JOIN Marks
	   	ON Students.StudentId = Marks.StudentId
		AND Plan.CourseId = Marks.CourseId
      WHERE Marks.Mark IS null
      GROUP BY Students.StudentId
      HAVING COUNT(DISTINCT Plan.CourseId) <= 2
) OR StudentId NOT IN (
      SELECT Students.StudentId
      FROM Students
      	   NATURAL JOIN Plan
	   LEFT JOIN Marks
	   	ON Students.StudentId = Marks.StudentId
		AND Plan.CourseId = Marks.CourseId
      WHERE Marks.Mark IS null
);
