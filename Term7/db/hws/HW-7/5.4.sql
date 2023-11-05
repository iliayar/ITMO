CREATE VIEW StudentDebts (StudentId, Debts) AS
SELECT
    Students.StudentId,
    COALESCE(D.Debts, 0) AS Debts
FROM
    Students
    LEFT JOIN (
        SELECT
            Students.StudentId,
            COUNT(DISTINCT Plan.CourseId) AS Debts
        FROM
            Students
            NATURAL JOIN Plan
            LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
                AND Plan.CourseId = Marks.CourseId
        WHERE
            Marks.Mark IS NULL
        GROUP BY
            Students.StudentId) D ON Students.StudentId = D.StudentId;

