HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
r(StudentId, StudentName, GroupName) :-
	     Students(StudentId, StudentName, GroupId),
	     Groups(GroupId, GroupName),
         Plan(GroupId, :CourseId, _),
	     not HasMark(StudentId, :CourseId).
