SELECT
    Courses.CourseName,
    G.GroupName
FROM
    Marks
    JOIN Courses ON Marks.CourseId = Courses.CourseId,
    Students AS S
    JOIN GROUPS AS G ON S.GroupId = G.GroupId
EXCEPT
SELECT
    CourseName,
    GroupName
FROM (
    SELECT
        Courses.CourseName,
        S.StudentId,
        G.GroupName
    FROM
        Marks
        JOIN Courses ON Marks.CourseId = Courses.CourseId,
        Students AS S
        JOIN GROUPS AS G ON S.GroupId = G.GroupId
EXCEPT
SELECT
    Courses.CourseName,
    Students.StudentId,
    Groups.GroupName
FROM
    Marks
    JOIN Courses ON Marks.CourseId = Courses.CourseId
    JOIN Students ON Marks.StudentId = Students.StudentId
    JOIN GROUPS ON Students.GroupId = Groups.GroupId) sq;

