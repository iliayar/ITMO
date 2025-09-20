UPDATE
    Students
SET
    GroupId = (
        SELECT
            GroupId
        FROM
            GROUPS
        WHERE
            GroupName = :GroupName)
WHERE
    GroupId IN (
        SELECT
            GroupId
        FROM
            GROUPS
        WHERE
            GroupName = :FromGroupName)
    AND EXISTS (
        SELECT
            GroupName
        FROM
            GROUPS
        WHERE
            GroupName = :GroupName);

