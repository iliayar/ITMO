-- PostgreSQL 14.9
CREATE FUNCTION AssertNoExtraMarks ()
    RETURNS TRIGGER
    LANGUAGE plpgsql
    AS $$
BEGIN
    IF NOT EXISTS (
SELECT * FROM Students AS s
        JOIN Plan AS p ON s.GroupId = p.GroupId
        JOIN Marks AS m ON s.StudentId = m.StudentId
        WHERE p.CourseId = m.CourseId
       -- SELECT
       --     *
       -- FROM
       --     Students
       --     JOIN Marks ON Students.StudentId = Marks.StudentId
       --     LEFT JOIN Plan ON Students.GroupId = Plan.GroupId
       --         AND Marks.CourseId = Plan.CourseId
       -- WHERE
       --     Plan.CourseId IS NULL
            ) THEN
        RAISE EXCEPTION 'There is students with marks for courses they dont study';
    END IF;
    RETURN NEW;
END;
$$;

CREATE CONSTRAINT TRIGGER NoExtraMarks
    AFTER UPDATE OR INSERT ON Marks
    FOR EACH ROW
    EXECUTE PROCEDURE AssertNoExtraMarks ();

CREATE CONSTRAINT TRIGGER NoExtraMarks
    AFTER UPDATE OR DELETE ON Plan
    FOR EACH ROW
    EXECUTE PROCEDURE AssertNoExtraMarks ();


CREATE CONSTRAINT TRIGGER NoExtraMarks
    AFTER UPDATE OR INSERT ON Students
    FOR EACH ROW
    EXECUTE PROCEDURE AssertNoExtraMarks ();
