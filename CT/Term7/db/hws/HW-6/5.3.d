HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
HasNoLecturerMark(StudentId) :-
			   Students(StudentId, _, _),
			   Lecturers(LecturerId, :LecturerName),
			   Plan(_, CourseId, LecturerId),
			   not HasMark(StudentId, CourseId).
r(StudentId) :-
	     Students(StudentId, _, _),
	     not HasNoLecturerMark(StudentId).