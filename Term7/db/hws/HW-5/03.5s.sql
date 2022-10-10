SELECT StudentId, StudentName, Students.GroupId
FROM Students
     NATURAL JOIN Marks
     JOIN Plan ON Marks.CourseId = Plan.CourseId
WHERE Mark = :Mark AND LecturerId = :LecturerId;
