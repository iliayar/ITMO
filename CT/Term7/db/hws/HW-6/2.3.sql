SELECT
	StudentId,
	StudentName,
	GroupName
FROM Students, Groups
WHERE Students.StudentId NOT IN (
      SELECT DISTINCT Marks.StudentId FROM Marks
      WHERE Marks.CourseId IN (
      	    SELECT Courses.CourseId
	    FROM Courses
	    WHERE Courses.CourseName = :CourseName
      )
)
      AND Students.GroupId = Groups.GroupId;
