HasDead(StudentId, CourseId) :- 
    Marks(StudentId, CourseId, Mark), 
    Mark > 2.
r(StudentName, CourseName) :-
	       Students(StudentId, StudentName, GroupId),
	       Courses(CourseId, CourseName),
           Plan(GroupId, CourseId, _),
	       not HasDead(StudentId, CourseId).
