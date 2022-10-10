-- 30 point 😞
SELECT StudentName, CourseName
FROM Students
     NATURAL JOIN Plan
     NATURAL JOIN Courses;
