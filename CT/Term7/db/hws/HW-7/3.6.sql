UPDATE Students AS S
SET Debts = (
    SELECT COUNT(DISTINCT Plan.CourseId)
    FROM Students
    	 NATURAL JOIN Plan
	 LEFT JOIN Marks
	      ON Students.StudentId = Marks.StudentId
	      AND Plan.CourseId = Marks.CourseId
    WHERE Students.StudentId = S.StudentId
    	  AND Marks.Mark IS null
)
WHERE 1 = 1;
