r(TeamName) :-
	    Teams(TeamId, TeamName),
	    Sessions(SessionId, TeamId, :ContestId, _),
	    Runs(_, SessionId, :Letter, _, 1).