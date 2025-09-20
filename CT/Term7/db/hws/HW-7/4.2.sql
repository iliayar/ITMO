UPDATE Marks AS M
SET Mark = (
    SELECT Mark
    FROM NewMarks
    WHERE NewMarks.StudentId = M.StudentId
    	  AND NewMarks.CourseId = M.CourseId
)
WHERE EXISTS (
    SELECT *
    FROM NewMarks
    WHERE NewMarks.StudentId = M.StudentId
          AND NewMarks.CourseId = M.CourseId
);
