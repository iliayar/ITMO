-- PostgreSQL 14.5
CREATE OR REPLACE FUNCTION RevertMarkUpdate()
RETURNS trigger
LANGUAGE plpgsql
AS $$
BEGIN
   UPDATE Marks
   SET Mark = OLD.Mark
   WHERE Marks.StudentId = OLD.StudentId
         AND Marks.CourseId = OLD.CourseId;
   RETURN NEW;
END;
$$;

CREATE OR REPLACE TRIGGER PreserveMarks AFTER UPDATE ON Marks
FOR EACH ROW
WHEN (NEW.Mark < OLD.Mark)
EXECUTE PROCEDURE RevertMarkUpdate();
