HasCourse(StudentId, CourseId) :- Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _).
HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
r(StudentName, CourseName) :-
	       Students(StudentId, StudentName, _),
	       Courses(CourseId, CourseName),
	       HasCourse(StudentId, CourseId),
	       not HasMark(StudentId, CourseId).