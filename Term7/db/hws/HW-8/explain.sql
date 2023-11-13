EXPLAIN SELECT StudentId, StudentName, GroupId FROM Students NATURAL JOIN Marks NATURAL JOIN Plan WHERE Mark = 5 AND LecturerId = :LecturerId;

