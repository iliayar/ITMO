SELECT DISTINCT StudentId
FROM Students
     NATURAL JOIN Marks
     NATURAL JOIN Plan
     NATURAL JOIN Lecturers
     Where Lecturers.LecturerName = :LecturerName;
