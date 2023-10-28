SELECT
    StudentId
FROM
    Students
EXCEPT
SELECT
    StudentId
FROM (
    SELECT
        Students.StudentId,
        Plan.CourseId
    FROM
        Students,
        Lecturers,
        Plan
    WHERE
        Lecturers.LecturerName = :LecturerName
        AND Plan.LecturerId = Lecturers.LecturerId
    EXCEPT
    SELECT
        StudentId,
        CourseId
    FROM
        Marks) sq;

