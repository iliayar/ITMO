SELECT StudentName, CourseName
FROM (
     SELECT StudentId, CourseId
     FROM Students, Plan
     WHERE Students.GroupId = Plan.GroupId
     UNION
     SELECT StudentId, CourseId
     FROM Marks
) AS SC, Students, Courses
WHERE SC.StudentId = Students.StudentId
      AND SC.CourseId = Courses.CourseId;
