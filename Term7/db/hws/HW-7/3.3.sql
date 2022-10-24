UPDATE Students
SET Marks = Students.Marks + (
    SELECT COUNT(*)
    FROM NewMarks
    WHERE NewMarks.StudentId = Students.StudentId
)
WHERE 1 = 1;
