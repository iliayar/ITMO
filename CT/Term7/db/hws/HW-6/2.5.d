HasMark(StudentId, CourseName) :- 
    Courses(CourseId, CourseName),
    Marks(StudentId, CourseId, _).
r(StudentId, StudentName, GroupName) :-
         Courses(CourseId, :CourseName),
	     Students(StudentId, StudentName, GroupId),
	     Groups(GroupId, GroupName),
         Plan(GroupId, CourseId, _),
	     not HasMark(StudentId, :CourseName).
