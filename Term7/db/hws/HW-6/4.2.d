HasCourse(StudentId, CourseId) :- Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _).
HasDead(StudentId, CourseId) :- Marks(StudentId, CourseId, Mark), Mark <= 2.
r(StudentName, CourseName) :-
	       Students(StudentId, StudentName, _),
	       Courses(CourseId, CourseName),
	       HasCourse(StudentId, CourseId),
	       HasDead(StudentId, CourseId).