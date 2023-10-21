SELECT
    StudentId,
    StudentName,
    Students.GroupId
FROM
    Students
    NATURAL JOIN Marks
    JOIN Plan ON Marks.CourseId = Plan.CourseId
    JOIN Lecturers ON Plan.LecturerId = Lecturers.LecturerId
WHERE
    Mark = :Mark
    AND LecturerName = :LecturerName;

