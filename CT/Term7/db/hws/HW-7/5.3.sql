CREATE VIEW Debts(StudentId, Debts) AS
SELECT Students.StudentId, COUNT(DISTINCT Plan.CourseId) AS Debts
FROM Students
     NATURAL JOIN Plan
     LEFT JOIN Marks
         ON Students.StudentId = Marks.StudentId
         AND Plan.CourseId = Marks.CourseId
WHERE Marks.Mark IS null
GROUP BY Students.StudentId;
