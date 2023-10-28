r(StudentId) :- 
    Students(StudentId, _, GroupId), 
    Plan(GroupId, CourseId, LecturerId), 
    Marks(StudentId, CourseId, _),
    Lecturers(LecturerId, :LecturerName).
