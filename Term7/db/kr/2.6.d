solved(SessionId, Letter) :-
	    Runs(_, SessionId, Letter, _, 1).
solvedAtLeastOne(ContestId, Letter) :-
    Sessions(SessionId, _, ContestId, _),
    solved(SessionId, Letter).
r(ProblemName) :-
	     Problems(ContestId, Letter, ProblemName),
	     not solvedAtLeastOne(ContestId, Letter).
