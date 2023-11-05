-- PostgreSQL 14.9
CREATE OR REPLACE FUNCTION RevertMarkUpdate ()
    RETURNS TRIGGER
    LANGUAGE plpgsql
    AS $$
BEGIN
    IF NEW.Mark < OLD.Mark THEN
        RETURN OLD;
    END IF;
    -- Changing student means old student will lose mark
    IF NEW.StudentId <> OLD.StudentId THEN
        RETURN OLD;
    END IF;
    -- Cannot remove mark (DELETE row or UPDATE Mark = NULL)
    IF NEW.Mark IS NULL THEN
        RAISE EXCEPTION 'Cannot remove mark';
    END IF;
    RETURN NEW;
END;
$$;

CREATE OR REPLACE TRIGGER PreserveMarks
    BEFORE UPDATE OR DELETE ON Marks
    FOR EACH ROW
    EXECUTE PROCEDURE RevertMarkUpdate ();

