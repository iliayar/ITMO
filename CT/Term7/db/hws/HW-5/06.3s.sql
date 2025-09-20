SELECT DISTINCT
    StudentId
FROM
    Marks
EXCEPT
SELECT
    StudentId
FROM (
    SELECT
        Marks.StudentId,
        Plan.CourseId
    FROM
        Marks,
        Plan
        JOIN Lecturers ON Plan.LecturerId = Lecturers.LecturerId
    WHERE
        LecturerName = :LecturerName
    EXCEPT
    SELECT
        StudentId,
        CourseId
    FROM
        Marks) sq;

