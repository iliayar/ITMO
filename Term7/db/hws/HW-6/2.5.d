HasCourse(StudentId, CourseName) :- Courses(CourseId, CourseName), Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _).
HasMark(StudentId, CourseName) :- Courses(CourseId, CourseName), Marks(StudentId, CourseId, _).
Helper(StudentId, StudentName, GroupName, CourseName) :-
	     Students(StudentId, StudentName, GroupId),
	     Groups(GroupId, GroupName),
	     HasCourse(StudentId, CourseName),
	     not HasMark(StudentId, CourseName).
r(StudentId, StudentName, GroupName) :- Helper(StudentId, StudentName, GroupName, :CourseName).