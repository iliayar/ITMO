DELETE FROM Students
WHERE StudentId NOT IN (
      SELECT DISTINCT StudentId
      FROM Marks
);
