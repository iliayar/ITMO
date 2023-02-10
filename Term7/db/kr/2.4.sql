SELECT ContestId, Letter
FROM Problems AS P
WHERE NOT EXISTS (
      SELECT *
      FROM Sessions
      	   NATURAL JOIN Runs
      WHERE P.ContestId = ContestId
      	    AND P.Letter = Letter
	    AND Accepted = 1
);
