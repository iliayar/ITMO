HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
HasNoLecturerMark(StudentId) :-
			   Students(StudentId, _, GroupId),
			   Lecturers(LecturerId, :LecturerName),
			   Plan(GroupId, CourseId, LecturerId),
			   not HasMark(StudentId, CourseId).
r(StudentId) :-
	     Students(StudentId, _, _),
	     not HasNoLecturerMark(StudentId).