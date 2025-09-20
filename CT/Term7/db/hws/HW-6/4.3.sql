SELECT
    StudentName,
    CourseName
FROM ( SELECT DISTINCT
        Students.StudentId,
        Plan.CourseId
    FROM
        Students,
        Plan
    WHERE
        Students.GroupId = Plan.GroupId
    EXCEPT
    SELECT
        Marks.StudentId,
        Plan.CourseId
    FROM
        Marks,
        Plan
    WHERE
        Marks.CourseId = Plan.CourseId
        AND Marks.Mark > 2) AS SC,
Students,
Courses
WHERE
    SC.StudentId = Students.StudentID
    AND SC.CourseId = Courses.CourseId;

