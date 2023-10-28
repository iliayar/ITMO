SELECT DISTINCT
    Students.StudentId,
    Students.StudentName,
    Groups.GroupName
FROM
    Students,
    GROUPS,
    Plan,
    Courses
WHERE
    Students.GroupId = Groups.GroupId
    AND Students.GroupId = Plan.GroupId
    AND Courses.CourseId = Plan.CourseId
    AND Courses.CourseName = :CourseName
EXCEPT
SELECT
    Marks.StudentId,
    Students.StudentName,
    Groups.GroupName
FROM
    Marks,
    Students,
    GROUPS,
    Courses
WHERE
    Marks.StudentId = Students.StudentId
    AND Students.GroupId = Groups.GroupId
    AND Marks.CourseId = Courses.CourseId
    AND Courses.CourseName = :CourseName;

