Solved(ContestId, Letter) :-
		  Sessions(SessionId, _, ContestId, _),
		  Runs(_, SessionId, Letter, _, 1).
r(ContestId, Letter) :-
	     Problems(ContestId, Letter, _),
	     not Solved(ContestId, Letter).