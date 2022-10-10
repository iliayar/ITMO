SELECT StudentId, StudentName, GroupId FROM Students NATURAL JOIN Marks NATURAL JOIN Courses WHERE Mark = :Mark AND CourseName = :CourseName;
