HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
StudentsWithNoMark(GroupId, CourseId) :-
			    Groups(GroupId, _),
			    Students(StudentId, _, GroupId),
			    Courses(CourseId, _),
			    not HasMark(StudentId, CourseId).
r(GroupId, CourseId) :-
	   Groups(GroupId, _),
	   Courses(CourseId, _),
	   not StudentsWithNoMark(GroupId, CourseId).
