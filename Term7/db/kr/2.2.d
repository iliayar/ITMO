solved(TeamId, ContestId, Letter) :-
	    Sessions(SessionId, TeamId, ContestId, _),
	    Runs(_, SessionId, Letter, _, 1).
r(TeamName) :-
	    Teams(TeamId, TeamName),
        not solved(TeamId, :ContestId, :Letter).
