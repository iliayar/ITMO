SELECT StudentId, StudentName, GroupId FROM Students NATURAL JOIN Marks NATURAL JOIN Plan WHERE Mark = :Mark AND LecturerId = :LecturerId;
