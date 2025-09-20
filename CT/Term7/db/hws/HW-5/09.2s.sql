SELECT StudentName, AVG(CAST(Mark AS FLOAT)) AS AvgMark
FROM Students
     LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
GROUP BY Students.StudentId, Students.StudentName;
