SELECT
    Marks.CourseId,
    Students.GroupId
FROM
    Marks,
    Students
EXCEPT
SELECT
    CourseId,
    GroupId
FROM (
    SELECT
        Marks.CourseId,
        Students.GroupId,
        Students.StudentId
    FROM
        Marks,
        Students
    EXCEPT
    SELECT
        Marks.CourseId,
        Students.GroupId,
        Students.StudentId
    FROM
        Marks
        JOIN Students ON Marks.StudentId = Students.StudentId) sq;

