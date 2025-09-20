SELECT
    Students.StudentId,
    COALESCE(T.Total, 0) AS Total,
    COALESCE(P.Passed, 0) AS Passed,
    COALESCE(T.Total, 0) - COALESCE(P.Passed, 0) AS Failed
FROM
    Students
    LEFT JOIN (
        SELECT
            Students.StudentId,
            COUNT(DISTINCT Plan.CourseId) AS Total
        FROM
            Students
            JOIN Plan ON Students.GroupId = Plan.GroupId
        GROUP BY
            Students.StudentId) T ON Students.StudentId = T.StudentId
    LEFT JOIN (
        SELECT
            Students.StudentId,
            COUNT(DISTINCT Marks.CourseId) AS Passed
        FROM
            Students
            JOIN Plan ON Students.GroupId = Plan.GroupId
            JOIN Marks ON Students.StudentId = Marks.StudentId
                AND Plan.CourseId = Marks.CourseId
        GROUP BY
            Students.StudentId) P ON Students.StudentId = P.StudentId;

