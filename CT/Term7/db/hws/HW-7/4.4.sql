MERGE INTO Marks
USING NewMarks
ON Marks.StudentId = NewMarks.StudentId
   AND Marks.CourseId = NewMarks.CourseId
WHEN MATCHED AND Marks.Mark < NewMarks.Mark
     THEN UPDATE SET Mark = NewMarks.Mark
WHEN NOT MATCHED
     THEN INSERT (StudentId, CourseId, Mark)
     VALUES (NewMarks.StudentId, NewMarks.CourseId, NewMarks.Mark);
