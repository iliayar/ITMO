SELECT
    StudentName,
    CourseName
FROM ( SELECT DISTINCT
        Students.StudentId,
        Plan.CourseId
    FROM
        Students,
        Plan,
        Marks
    WHERE
        Students.GroupId = Plan.GroupId
        AND Students.StudentId = Marks.StudentId
        AND Marks.CourseId = Plan.CourseId
        AND Marks.Mark <= 2) SC,
    Students,
    Courses
WHERE
    SC.StudentId = Students.StudentID
    AND SC.CourseId = Courses.CourseId;

