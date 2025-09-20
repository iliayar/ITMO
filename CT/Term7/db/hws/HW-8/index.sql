  CREATE UNIQUE INDEX StudentsStudentName ON Students USING BTREE (StudentName text_pattern_ops, GroupId);
DROP INDEX StudentsStudentName;
