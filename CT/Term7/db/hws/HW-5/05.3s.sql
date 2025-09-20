SELECT
    StudentName,
    CourseName
FROM (
    SELECT
        StudentId,
        CourseId,
        StudentName,
        CourseName
    FROM
        Students
    NATURAL JOIN Plan
    NATURAL JOIN Courses
EXCEPT
SELECT
    StudentId,
    CourseId,
    StudentName,
    CourseName
FROM
    Students
    NATURAL JOIN Marks
    NATURAL JOIN Courses
WHERE
    Marks.Mark = 5
    OR Marks.Mark = 4) InnerQuery;

