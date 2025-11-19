#import "common.typ": *

#show: doc => hw(10, doc)

#line(length: 100%)
#task()[]
#proof()[
  По условию пусть $A = {omega in Omega : xi_n (omega) -> xi(omega)}, B = {omega in Omega : xi_n (omega) -> eta(omega)}$ тогда $PP(A) = PP(B) = 1$. Заметим что $A^C union B^C = (A inter B)^C$.
  $ PP(A^C) = 1 - PP(A) = 0 quad PP(B^C) = 1 - PP(B) = 0 $
  $ PP(A^C union B^C) <= PP(A^C) + PP(B^C) = 0 ==> PP(A^C union B^C) = 0 $
  $ PP((A inter B)^C) = 1 - PP(A inter B) = PP(A^C union B^C) = 0 ==> PP(A inter B) = 1 $
  Получается что $A inter B = {omega in Omega : xi_n (omega) -> xi(omega) and xi_n (omega) -> eta(omega)}$. По единственности предела $xi_n (omega) -> xi(omega) and xi_n (omega) -> eta(omega) <==> xi = eta$. Тогда
  $ PP(A inter B) = PP({omega in Omega : xi(omega) = eta(omega)}) = PP(xi = eta) = 1 $
]

#line(length: 100%)
#task()[]
#proof()[
  По условию $forall epsilon > 0 quad PP(|xi_n - xi| > epsilon) -> 0 quad PP(|xi_n - eta| > epsilon) -> 0$.
  По неравенству треугольника $|xi - xi_n| + |xi_n - eta| >= |xi - eta|$. Можно заметить что если $|xi - xi_n| + |xi_n - eta| > epsilon$, то либо $|xi - xi_n| > epsilon / 2$ либо $|xi_n - eta| > epsilon /2$, тогда:
  $ {omega in Omega : |xi(omega) - xi_n (omega)| + |xi_n (omega) - eta (omega)| > epsilon} subset {omega in Omega : |xi(omega) - xi_n (omega)| > epsilon / 2} union {omega in Omega : |xi_n (omega) - eta(omega)| > epsilon / 2} $
  Также заметим что если $|xi - eta| > epsilon$, то $|xi - xi_n| + |xi_n - eta| > epsilon$, а значит:
  $ {omega in Omega : |xi (omega) - eta (omega)| > epsilon} subset {omega in Omega : |xi(omega) - xi_n (omega)| + |xi_n (omega) - eta (omega)| > epsilon} $
  Тогда
  $ PP(|xi - eta| > epsilon) <= PP(|xi - xi_n| > epsilon / 2) + PP(|xi_n - eta| > epsilon / 2) -> 0 ==> PP(|xi - eta| > epsilon) = 0 $
  Можно сказать что если для любых $epsilon > 0$ $PP(|xi - eta| > epsilon) -> 0$, то $PP(xi != eta) -> 0$. А значит $PP(xi = eta) = 1$.
]

#line(length: 100%)
#task()[]
#proof()[
  По теорему Слуцкого если $xi_n ->^d xi$ и $eta_n ->^PP C$, то $xi_n ->^d xi dot C$. Применим для нашего случая:
  $ xi_n eta_n ->^d xi dot 0 ==> xi_n eta_n ->^d 0 $

  По свойству $xi_n ->^d C ==> xi_n ->^PP C$ (доказанному на практике), $xi_n eta_n ->^PP 0$
]
