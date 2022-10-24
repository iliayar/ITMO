CREATE VIEW AllMarks(StudentId, Marks) AS
SELECT SM.StudentId, COUNT(SM.Mark) AS Marks
FROM (
     SELECT Students.StudentId, Mark
     FROM Students
     	  LEFT JOIN Marks
	       ON Students.StudentId = Marks.StudentId
     UNION ALL
     SELECT Students.StudentId, Mark
     FROM Students
     	  LEFT JOIN NewMarks
	       ON Students.StudentId = NewMarks.StudentId
) SM
GROUP BY StudentId;
