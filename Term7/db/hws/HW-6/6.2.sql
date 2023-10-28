SELECT
    Groups.GroupName,
    Courses.CourseName
FROM (
    SELECT
        Groups.GroupId,
        Courses.CourseId
    FROM
        GROUPS,
        Courses
    EXCEPT
    SELECT
        GroupId,
        CourseId
    FROM (
        SELECT
            Students.StudentId,
            Students.GroupId,
            Courses.CourseId
        FROM
            Students,
            Courses
        EXCEPT
        SELECT
            Students.StudentId,
            Students.GroupId,
            Marks.CourseId
        FROM
            Students,
            Marks
        WHERE
            Students.StudentId = Marks.StudentId) sq) GC,
GROUPS,
Courses
WHERE
    GC.GroupId = Groups.GroupId
    AND GC.CourseId = Courses.CourseId;

