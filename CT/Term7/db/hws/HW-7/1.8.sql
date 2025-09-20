DELETE FROM Students
WHERE StudentId NOT IN (
        SELECT
            Students.StudentId
        FROM
            Students
        NATURAL JOIN Plan
        LEFT JOIN Marks ON Students.StudentId = Marks.StudentId
            AND Plan.CourseId = Marks.CourseId
    WHERE
        Marks.Mark IS NULL
    GROUP BY
        Students.StudentId
    HAVING
        COUNT(DISTINCT Plan.CourseId) > 2);

