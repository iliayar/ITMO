HasCourse(StudentId, CourseId) :- Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _).
HasMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
Helper(StudentId, StudentName, GroupName, CourseId) :-
	     Students(StudentId, StudentName, GroupId),
	     Groups(GroupId, GroupName),
	     HasCourse(StudentId, CourseId),
	     not HasMark(StudentId, CourseId).
r(StudentId, StudentName, GroupName) :- Helper(StudentId, StudentName, GroupName, :CourseId).