r(StudentName, CourseName) :-
	       Students(StudentId, StudentName, GroupId),
	       Courses(CourseId, CourseName),
           Plan(GroupId, CourseId, _),
           Marks(StudentId, CourseId, Mark),
           Mark <= 2.
