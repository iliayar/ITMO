SELECT StudentName, SUM(Mark) AS SumMark
FROM Students
     LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
GROUP BY Students.StudentId, Students.StudentName;
