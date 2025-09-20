solved(SessionId, ContestId, Letter) :-
	    Sessions(SessionId, _, ContestId, _),
	    Runs(_, SessionId, Letter, _, 1).
notSolvedAny(ContestId, Letter) :-
    Problems(ContestId, Letter, _),
    Sessions(SessionId, _, ContestId, _),
    not solved(SessionId, ContestId, Letter).
r(ContestId, Letter) :-
	     Problems(ContestId, Letter, _),
	     not notSolvedAny(ContestId, Letter).
