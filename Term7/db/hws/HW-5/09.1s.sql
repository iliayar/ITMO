SELECT AVG(CAST(Mark AS FLOAT)) AS AvgMark
FROM Marks
WHERE StudentId = :StudentId;
