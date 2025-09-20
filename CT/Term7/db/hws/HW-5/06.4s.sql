SELECT DISTINCT
    StudentId
FROM (
    SELECT
        Students.StudentId,
        P1.GroupId
    FROM
        Students
        JOIN Plan ON Students.GroupId = Plan.GroupId
        JOIN Lecturers ON Lecturers.LecturerId = Plan.LecturerId
        JOIN Marks ON Students.StudentId = Marks.StudentId
            AND Plan.CourseId = Marks.CourseId,
            Plan AS P1
        JOIN Lecturers AS L1 ON P1.LecturerId = L1.LecturerId
    WHERE
        Lecturers.LecturerName = :LecturerName
        AND L1.LecturerName = :LecturerName
    EXCEPT
    SELECT
        StudentId,
        GroupId
    FROM (
        SELECT
            Students.StudentId,
            P1.CourseId,
            P1.GroupId
        FROM
            Students
            JOIN Plan ON Students.GroupId = Plan.GroupId
            JOIN Lecturers ON Lecturers.LecturerId = Plan.LecturerId
            JOIN Marks ON Students.StudentId = Marks.StudentId
                AND Plan.CourseId = Marks.CourseId,
                Plan AS P1
            JOIN Lecturers AS L1 ON P1.LecturerId = L1.LecturerId
        WHERE
            Lecturers.LecturerName = :LecturerName
            AND L1.LecturerName = :LecturerName
        EXCEPT
        SELECT
            Students.StudentId,
            Marks.CourseId,
            Plan.GroupId
        FROM
            Students
            JOIN Plan ON Students.GroupId = Plan.GroupId
            JOIN Lecturers ON Lecturers.LecturerId = Plan.LecturerId
            JOIN Marks ON Students.StudentId = Marks.StudentId
                AND Plan.CourseId = Marks.CourseId
        WHERE
            Lecturers.LecturerName = :LecturerName) sq2) sq1;

