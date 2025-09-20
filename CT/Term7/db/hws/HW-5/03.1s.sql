SELECT StudentId, StudentName, GroupId FROM Students NATURAL JOIN Marks WHERE Mark = :Mark AND CourseId = :CourseId;
