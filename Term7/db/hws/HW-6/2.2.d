WithMark(StudentId, CourseId) :- Marks(StudentId, CourseId, _).
r(StudentId, StudentName, GroupName) :- Students(StudentId, StudentName, GroupId), Groups(GroupId, GroupName), not WithMark(StudentId, :CourseId).
