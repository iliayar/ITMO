DELETE FROM Students
WHERE StudentId IN (
      SELECT StudentId
      FROM Marks
      GROUP BY StudentId
      HAVING COUNT(StudentId) >= 3
);
