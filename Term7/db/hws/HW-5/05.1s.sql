SELECT StudentName, CourseName FROM (
    SELECT DISTINCT StudentId, Plan.CourseId FROM Plan
    JOIN Courses ON Plan.CourseId = Courses.CourseId
    JOIN Students ON Students.GroupId = Plan.GroupId
) sq
JOIN Students ON Students.StudentId = sq.StudentId
JOIN Courses ON Courses.CourseId = sq.CourseId;
