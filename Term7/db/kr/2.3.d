r(TeamId) :-
	    Sessions(SessionId, TeamId, :ContestId, _),
	    Runs(_, SessionId, _, _, 1).