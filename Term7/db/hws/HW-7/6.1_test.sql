-- OK: Change row in Marks
UPDATE
    Marks
SET
    CourseId = 2
WHERE
    StudentId = 1
    AND CourseId = 1;

SELECT
    *
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 2;

UPDATE
    Marks
SET
    StudentId = 3
WHERE
    StudentId = 1
    AND CourseId = 1;

SELECT
    *
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 2;

DELETE FROM Marks
WHERE StudentId = 3
    AND CourseId = 3;

SELECT
    *
FROM
    Marks
WHERE
    StudentId = 3
    AND CourseId = 3;

-- FAIL: Change row in Marks
UPDATE
    Marks
SET
    CourseId = 5
WHERE
    StudentId = 1
    AND CourseId = 2;

SELECT
    *
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 2;

UPDATE
    Marks
SET
    StudentId = 3
WHERE
    StudentId = 1
    AND CourseId = 2;

SELECT
    *
FROM
    Marks
WHERE
    StudentId = 1
    AND CourseId = 2;

-- FAIL: Change row in plan
UPDATE
    Plan
SET
    GroupId = 10
WHERE
    CourseId = 2;

SELECT
    *
FROM
    Plan
WHERE
    CourseId = 2;

UPDATE
    Plan
SET
    CourseId = 10
WHERE
    CourseId = 2;

SELECT
    *
FROM
    Plan
WHERE
    CourseId = 2;

DELETE FROM Plan
WHERE CourseId = 2;

SELECT
    *
FROM
    Plan
WHERE
    CourseId = 2;

