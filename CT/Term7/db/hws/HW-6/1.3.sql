SELECT StudentId, StudentName, GroupId
FROM Students
WHERE StudentId IN (
      SELECT Marks.StudentId
      FROM Marks
      WHERE CourseId = :CourseId
      	    AND Mark = :Mark
);
