r(StudentId, CourseId) :- Students(StudentId, _, GroupId), Plan(GroupId, CourseId, _).
r(StudentId, CourseId) :- Marks(StudentId, CourseId, _).