CREATE VIEW StudentDebts(StudentId, Debts) AS
SELECT Students.StudentId, COUNT(DISTINCT Plan.CourseId) AS Debts
FROM Students
     NATURAL JOIN Plan
     LEFT JOIN Marks
         ON Students.StudentId = Marks.StudentId
         AND Plan.CourseId = Marks.CourseId
WHERE Marks.Mark IS null
GROUP BY Students.StudentId

UNION ALL

SELECT DISTINCT S.StudentId, 0 AS Debts
FROM Students AS S
WHERE NOT EXISTS (
      SELECT *
      FROM Students
      	   NATURAL JOIN Plan
	   LEFT JOIN Marks
	   	ON Students.StudentId = Marks.StudentId
		AND Plan.CourseId = Marks.CourseId
      WHERE Students.StudentId = S.StudentId
      	    AND Marks.Mark IS null
);
