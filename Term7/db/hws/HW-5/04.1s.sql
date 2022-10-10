SELECT StudentId, StudentName, GroupId FROM Students
       EXCEPT SELECT StudentId, StudentName, GroupId
       	      FROM Students
	      NATURAL JOIN Marks
	      NATURAL JOIN Courses
	      WHERE CourseName = :CourseName;
