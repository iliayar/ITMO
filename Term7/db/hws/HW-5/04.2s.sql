SELECT StudentId, StudentName, GroupId
FROM Students
     NATURAL JOIN Plan
     NATURAL JOIN Courses
     WHERE CourseName = :CourseName
       EXCEPT SELECT StudentId, StudentName, GroupId
       	      FROM Students
	      	   NATURAL JOIN Marks
	      	   NATURAL JOIN Courses
	      WHERE CourseName = :CourseName;
