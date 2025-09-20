UPDATE Students
SET Marks = (
    SELECT COUNT(*)
    FROM Marks
    WHERE Marks.StudentId = Students.StudentId
)
WHERE 1 = 1;
