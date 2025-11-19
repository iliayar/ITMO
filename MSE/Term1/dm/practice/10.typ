#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 10],
  date: [10 ноября],
  number: 10,
  doc
)

#task(numbering: (..) => numbering("1.a", 1, 1))[
  Пусть $xi_n --> xi$ почти наверное и $g(xi_b) --> g(xi)$ почти наверное
]
#proof()[
  $ PP({omega in Omega : g(xi_n(omega)) --> g(xi(omega))}) =^((?)) 1 $
  Хотим показать что $xi_n (omega) --> xi(omega)$, то $g(xi_n(omega)) --> g(xi(omega))$. $g(x)$ --- непрерывна
  $ {omega in Omega : xi_n(omega) --> xi(omega) } subset {omega in Omega : g(xi_n(omega)) --> g(xi(omega))) } $
  $ PP({omega in Omega : xi_n(omega) --> xi(omega) }) <= PP({omega in Omega : g(xi_n(omega)) --> g(xi(omega))) }) $
  Левая часть ясно что $1$, правая часть $>= 1$, а т.к. это вероятность, то она тоже $1$.
]

#task(numbering: (..) => numbering("1.a", 1, 2))[]
#solution()[
  Чтобы показать что $g(xi_n, eta_n) --> g(xi, eta)$, то нужно на ${omega in Omega : g(xi_n, eta_n) --> g(xi, eta)}$ навесить $PP$ и показать что оно равно $1$.

  $ {omega in Omega : xi_n --> xi, eta_n --> eta} subset {omega in Omega : g(xi_n, eta_n) --> g(xi, eta)}$
  $ PP(omega in Omega : xi_n arrow.not xi or eta_n arrow.not eta) <= PP(xi_n arrow.not xi) + PP(eta_n arrow.not eta) = 0 $
  $ 1 = PP({omega in Omega : xi_n --> xi, eta_n --> eta}) <= PP({omega in Omega : g(xi_n, eta_n) --> g(xi, eta)}) $
]

#task(numbering: (..) => numbering("1.a", 2, 1))[]
#solution()[
  $xi_n -->^p c <==> forall delta > 0, PP(|xi_n - c| > delta) --> 0$. Нужно доказать что $forall epsilon > 0, PP(|g(xi_n) - g(c)| > epsilon)$
  $ forall epsilon > 0, exists delta : |xi_n - c| <= delta \" & subset\" |g(xi_n) - g(c)| <= epsilon  \
                                       1 <- PP(|xi_n - c| <= delta) & <= PP(g(xi_n) - g(c)) -> 1
  $
]

#task(numbering: (..) => numbering("1.a", 2, 2))[]
#solution()[#todo()]

#task(numbering: (..) => numbering("1.a", 2, 3))[]
#solution()[
  Условие равномерной непрерывности
  $ forall epsilon > 0, exists delta > 0 : ||(xi_n, eta_n) - (xi, eta)|| <= delta ==> |g(xi_n, eta_n) - g(xi, eta)| <= epsilon $
  $ PP(||(xi_n, eta_n) - (xi, eta)|| > delta) <= PP(|xi_n - xi| > delta/4) + PP(|eta_n - eta| > delta/4) $
  В правую часть входит строго больше событий чем в левую
  $ sqrt((xi_n - x)^2 + (eta_n - eta)^2) > delta quad sqrt((delta / 4)^2 + (delta / 4)^2) = delta/(2sqrt(2)) $
  По условию ($xi_n -->^p xi$, $eta_n -->^p eta$) $PP(|xi_n - xi| > delta/4) --> 0$ и $PP(|eta_n - eta| > delta/4) --> 0$.
  Это значит что 
  $ PP(||(xi_n, eta_n) - (xi, eta)|| > delta) --> 0 ==> PP(||(xi_n, eta_n) - (xi, eta)|| <= delta) -> 1 ==> PP(|g(xi_n, eta_n) - g(xi, eta)| <= epsilon) -->1 $

]

#task(numbering: (..) => numbering("1", 3))[
  Пусть $xi_n -->^d c$. Докажите что тогда $xi_n -->^PP c$
]
#solution()[
  $F_(xi_n) (x) --> F_c (x) quad forall x in C_(F_(xi_n))$. Заметим что $F_c(x) = PP(c <= x)$. При $x < c$ $F_(xi_n) (x) --> 0$, а при $x > c$ $F_(xi_n) (x) --> 1$. Хотим доказать что $forall epsilon > 0 : PP(|xi_n - c| <= epsilon) --> 1$
  $ PP(-epsilon + c <= xi_n <= xi + c) = underbrace(F_(xi_n) (c + epsilon), --> 1) - underbrace(F(xi_n) (c - epsilon), --> 0) + PP(xi_n = c - epsilon) $
  $ PP(xi_n <= c - epsilon/2) = PP(xi_n <= (3 epsilon) / 2) + PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]) $
  $ underbrace(PP(xi_n <= c - epsilon/2), --> 0) - underbrace(PP(xi_n <= (3 epsilon) / 2), --> 0) = PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]) $
  $ underbrace(PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]), --> 0) <= PP(c - epsilon - xi_n) --> 0 $
]

#task(numbering: (..) => numbering("1", 3))[
  Докажите, что если $xi_n -->^d xi$ и $eta_n -->^PP c$, то $xi_n + eta_n -->^d xi + c$
]
#solution()[
  Нужно показать что $ forall x in C_(xi + c) : F_(xi_n + eta_n) (x) --> F_(xi + c) (x)$, либо $F_(xi_n + eta_n) (x) = PP(xi_n + eta_n <= x) --> PP(xi + c <= x)$.
  $ PP(xi_n + eta_n <= x) = PP(xi_n + eta_n <= x, |eta_n - c| < epsilon) + PP(xi_n + eta_n <= x, |eta_n - c| >= epsilon) $
  $ PP(xi_n + eta_n <= x, |eta_n - c| >= epsilon) <= PP(|eta_n - c| >= epsilon) --> 0 $
  Осталось показать что $PP(xi_n + eta_n <= x, |eta_n - c| < epsilon) --> PP(xi + c <= x)$.
  $ c - epsilon < eta_n < c + epsilon $
  $ dots c - epsilon dots <= PP(xi_n + eta_n <= x, |eta_n - c| < epsilon) <= dots c + epsilon dots $
  Скажем что $PP(A') >= c - epsilon$, и $PP(A') = F_(xi_n) (x - c + epsilon)$.
  #todo()
]
