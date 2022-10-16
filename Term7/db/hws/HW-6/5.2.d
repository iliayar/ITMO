HasMark(StudentId, LecturerName) :-
		   Students(StudentId, _, GroupId),
		   Marks(StudentId, CourseId, _),
		   Lecturers(LecturerId, LecturerName),
		   Plan(GroupId, CourseId, LecturerId).
r(StudentId) :- Students(StudentId, _, _), not HasMark(StudentId, :LecturerName).
