SELECT
    StudentId
FROM
    Students
EXCEPT
SELECT
    Students.StudentId
FROM
    Marks
    NATURAL JOIN Students
    NATURAL JOIN Plan
    NATURAL JOIN Lecturers
WHERE
    Lecturers.LecturerName = :LecturerName;

