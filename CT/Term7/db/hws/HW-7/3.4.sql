UPDATE Students
SET Marks = (
    SELECT COUNT(DISTINCT Marks.CourseId)
    FROM Marks
    WHERE Marks.StudentId = Students.StudentId
)
WHERE 1 = 1;
