SELECT GroupName, AVG(CAST(Mark AS FLOAT)) AS AvgMark
FROM Groups
     LEFT JOIN Students ON Groups.GroupId = Students.GroupId
     LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
GROUP BY Groups.GroupId, Groups.GroupName;
