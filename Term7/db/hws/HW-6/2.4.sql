SELECT DISTINCT
    Students.StudentId,
    Students.StudentName,
    Groups.GroupName
FROM
    Students,
    GROUPS,
    Plan
WHERE
    Students.GroupId = Groups.GroupId
    AND Students.GroupId = Plan.GroupId
    AND Plan.CourseId = :CourseId
EXCEPT
SELECT
    Marks.StudentId,
    Students.StudentName,
    Groups.GroupName
FROM
    Marks,
    Students,
    GROUPS
WHERE
    Marks.StudentId = Students.StudentId
    AND Students.GroupId = Groups.GroupId
    AND Marks.CourseId = :CourseId;

