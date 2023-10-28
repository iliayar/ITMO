r(StudentName, CourseName) :- 
    Students(StudentId, StudentName, GroupId), 
    Plan(GroupId, CourseId, _), 
    Courses(CourseId, CourseName).
r(StudentName, CourseName) :- 
    Marks(StudentId, CourseId, _),
    Students(StudentId, StudentName, _),
    Courses(CourseId, CourseName).
