SELECT DISTINCT
    Students.StudentId
FROM
    Students,
    Plan,
    Marks,
    Lecturers
WHERE
    Plan.GroupId = Students.GroupId
    AND Plan.LecturerId = Lecturers.LecturerId
    AND Marks.StudentId = Students.StudentId
    AND Marks.CourseId = Plan.CourseId
    AND Lecturers.LecturerId = Plan.LecturerId
    AND Lecturers.LecturerName = :LecturerName;

