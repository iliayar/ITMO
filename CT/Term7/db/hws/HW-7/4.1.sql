INSERT INTO Marks (StudentId, CourseId, Mark)
SELECT
    NewMarks.StudentId,
    NewMarks.CourseId,
    NewMarks.Mark
FROM
    NewMarks
    LEFT JOIN Marks ON NewMarks.StudentId = Marks.StudentId
        AND NewMarks.CourseId = Marks.CourseId
WHERE
   Marks.Mark IS NULL
