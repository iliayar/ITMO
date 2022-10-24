UPDATE Students
SET Marks = (
    SELECT COUNT(*)
    FROM Marks
    WHERE StudentId = :StudentId
)
WHERE StudentId = :StudentId;
