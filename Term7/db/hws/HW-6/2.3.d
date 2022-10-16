WithMark(StudentId, CourseName) :- Courses(CourseId, CourseName), Marks(StudentId, CourseId, _).
r(StudentId, StudentName, GroupName) :-
	     Students(StudentId, StudentName, GroupId),
	     Groups(GroupId, GroupName),
	     not WithMark(StudentId, :CourseName).
