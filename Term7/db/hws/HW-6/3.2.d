Helper(StudentId, StudentName, CourseId, CourseName) :- Students(StudentId, StudentName, _), Courses(CourseId, CourseName).
r(StudentName, CourseName) :- Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _), Helper(StudentId, StudentName, CourseId, CourseName).
r(StudentName, CourseName) :- Marks(StudentId, CourseId, _), Helper(StudentId, StudentName, CourseId, CourseName).