CREATE VIEW AllMarks (StudentId, Marks) AS
SELECT
    Students.StudentId,
    COUNT(M.Mark) AS Marks
FROM
    Students
    LEFT JOIN (
        SELECT
            StudentId,
            Mark
        FROM
            Marks
    UNION ALL
    SELECT
        StudentId,
        Mark
    FROM
        NewMarks) M ON Students.StudentId = M.StudentId
GROUP BY
    Students.StudentId;

