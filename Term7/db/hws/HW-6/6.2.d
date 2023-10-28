HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
StudentsWithNoMark(GroupId, CourseId) :-
			    Students(StudentId, _, GroupId),
			    Courses(CourseId, _),
			    not HasMark(StudentId, CourseId).
r(GroupName, CourseName) :-
	   Groups(GroupId, GroupName),
	   Courses(CourseId, CourseName),
	   not StudentsWithNoMark(GroupId, CourseId).
