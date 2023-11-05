UPDATE
    Marks
SET
    Mark = 3
WHERE
    StudentId = 1
    AND CourseId = 1;

SELECT
    Mark
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 1;

UPDATE
    Marks
SET
    StudentId = 10
WHERE
    StudentId = 1
    AND CourseId = 1;

SELECT
    Mark
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 1;

DELETE FROM Marks
WHERE StudentId = 1
    AND CourseId = 1;

SELECT
    Mark
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 1;
