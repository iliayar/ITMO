HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
r(StudentName, CourseName) :-
	       Students(StudentId, StudentName, GroupId),
	       Courses(CourseId, CourseName),
           Plan(GroupId, CourseId, _),
	       not HasMark(StudentId, CourseId).
