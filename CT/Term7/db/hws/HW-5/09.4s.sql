SELECT
    GroupName,
    AVG(CAST(AvgMark AS float)) AS AvgAvgMark
FROM (
    SELECT
        Students.StudentId,
        Students.StudentName,
        Groups.GroupId,
        Groups.GroupName,
        AVG(CAST(Mark AS float)) AS AvgMark
    FROM
        Groups
    LEFT JOIN Students ON Groups.GroupId = Students.GroupId
    LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
GROUP BY
    Groups.GroupId,
    Groups.GroupName,
    Students.StudentId,
    Students.StudentName) sq
GROUP BY
    GroupId,
    GroupName;

