sieve(N, _, Max) :- 
	N > Max.
sieve(N, Step, Max) :-
	sieve_single(N, Step),
	Next is N + Step,
	sieve(Next, Step, Max).

sieve_single(N, _) :-
	composite(N).
sieve_single(N, Prime) :-
	assert(composite(N)),
	assert(min_divisor(N, Prime)).
	
sieve(N, Max) :- 
	(N * N) > Max.
sieve(N, Max) :-
	(prime(N),
	Start is N * N,
	sieve(Start, N, Max);
	true),
	Next is N + 1,
	sieve(Next, Max).

composite(1).
init(Max) :-
	sieve(2, Max).

prime(N) :- 
	\+ composite(N).
	

prime_divisors(N, Divisors) :-
	var(N), !,
	divisors_multiply(N, Divisors, 2).

divisors_multiply(1, [], _).
divisors_multiply(N, [H | T], Min) :-
	H >= Min,
	prime(H),
	divisors_multiply(Next, T, H),
	N is Next * H.
	
prime_divisors(1, []).
prime_divisors(N, [N]) :-
	prime(N).
prime_divisors(N, [H | T]) :-
	min_divisor(N, H),
	Next is div(N, H),
	prime_divisors(Next, T).

prime_palindrome(N, K) :-
	prime(N),
	convert_ns(N, K, R),
	reverse(R, R).

convert_ns(0, _, []) :- !.
convert_ns(N, K, [H | T]) :-
	H is mod(N, K),
	Next is div(N, K),
	convert_ns(Next, K, T).

nth_prime(N, P) :-
	nth_prime(0, N, P).

nth_prime(I, 0, P) :-
	P is I, !.
nth_prime(I, N, P) :-
	NextI is I + 1,
	(composite(NextI) -> 
		NextN is N;
		NextN is N - 1),
		nth_prime(NextI, NextN, P).
		
