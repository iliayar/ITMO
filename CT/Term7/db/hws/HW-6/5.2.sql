SELECT DISTINCT
    StudentId
FROM
    Students
EXCEPT
SELECT
    Students.StudentId
FROM
    Students,
    Marks,
    Lecturers,
    Plan
WHERE
    Marks.StudentId = Students.StudentId
    AND Lecturers.LecturerName = :LecturerName
    AND Plan.GroupId = Students.GroupId
    AND Plan.CourseId = Marks.CourseId
    AND Plan.LecturerId = Lecturers.LecturerId;
