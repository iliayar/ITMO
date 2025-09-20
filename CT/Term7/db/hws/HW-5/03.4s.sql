SELECT
    StudentId,
    StudentName,
    GroupId
FROM
    Students
    NATURAL JOIN Marks
    NATURAL JOIN Plan
    NATURAL JOIN Lecturers
WHERE
    Mark = :Mark
    AND LecturerName = :LecturerName;

