#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 2],
  date: [26 февраля],
  number: 2,
  doc
)

$X_1, dots, X_n ~ P_Theta$. Не знаем $Theta$ но хотим понять

#remark[
  $forall theta in Theta med T_n ->^(PP_Theta) theta$
]

#remark[
  Неравенство Чебышева: $DD xi < infinity ==> PP(|xi - EE xi| > epsilon) <= (D xi) / epsilon^2$
]
#task(numbering: (..) => numbering("1.a", 1, 1))[
  Хотим показать что $forall theta in T_n ->^PP theta$

  Пусть $T_n$ *несмещенная* оценка. Т.е. $forall theta in Theta med EE_theta T_n = theta$.

  По неравенству Чебышева $forall theta in Theta med forall epsilon > 0 med PP(|T_n - EE_theta T_n| > epsilon) < (DD_theta T_n) / epsilon^2 ->^(n -> +infinity) 0$. Т.е. $T_n ->^PP theta (= EE_theta T_n)$
]

#task(numbering: (..) => numbering("1", 1))[
  Хотим показать что $forall theta in T_n ->^PP theta$

  Пусть $T_n$ *ассимптотически несмещенная* оценка. Т.е. $forall theta in Theta med EE_theta T_n ->_(n -> +infinity) theta$.
  $ PP_theta ( |T_n - EE_theta T_n + EE_theta T_n - theta | > epsilon) <= PP_theta ( |T_n - EE_theta T_n| + |EE_theta T_n - theta | > epsilon) $
  Т.к. $|T_n - EE_theta T_n| + |EE_theta T_n - theta| >= |T_n - theta| >= epsilon$
  $ PP_theta ( |T_n - EE_theta T_n| + |EE_theta T_n - theta | > epsilon) <= PP_theta (|T_n - EE_theta T_n| > epsilon / 2) ->_(n -> infinity) 0$
  по Чебышеву
]
#remark[
  По Маркову:
  $ PP_theta (|T_n - theta| > epsilon) = PP_theta (|T_n - theta|^2 > epsilon^2) <= (EE_theta (T_n - theta)^2) / epsilon^2 $
  Но $EE_theta (T_n - theta) = DD T_n + (EE_theta T_n - theta)^2$, где оба слагаемых $-> 0$.
]

#task(numbering: (..) => numbering("1", 2))[
  $xi_1, dots, xi_n$ --- выборка из распределения с ф.р. $F$. $xi_((n)) = max(xi_1, dots, xi_n)$. Хоти найти $F_(xi_((n))) (x) = PP(xi_((n)) <= x) = PP(xi_1 <= x) dot PP(xi_2 <= x) dot dots dot PP(xi_n <= x) = F^n(x)$, т.к. одинаков распределенные величины.

]

#task(numbering: (..) => numbering("1", 3))[
  $f(x)$ --- плотность. $F(x) = integral_(-infinity)^x f(d) d t$. Имеем $f(x) = F'(x)$ почти везде.
  $ f(x) = (F^n (x))' = n dot F^(n - 1) (x) dot f(x) $
]

#task(numbering: (..) => numbering("1", 4))[]
#solution[
  $xi_1, dots, x_n ~ U[0; theta]$. $f_(xi_i) (x) = cases(1 / Theta quad & x in [0; theta], 0 & #text[иначе])$
  1.
    $ EE_theta [2 overline(xi)] = EE_theta [2 dot 1/ n sum_(i = 1)^n xi_i] = 2/n sum_(i = 1)^n EE_theta xi_i = 2/n dot n dot theta / 2 = theta $
    По ЗБЧ(?)
    $ overline(xi) ->^(PP_theta) EE_theta xi_i = theta / 2 ==> 2 overline(xi) ->^(PP_theta) 2 EE_theta xi_i = theta $
    Состоятельная и несмещенная
  2.
    $ F_(xi_i) = cases(x / theta quad & x in [0; theta], 1 & x > theta, 0 & x < theta) $
    $ EE_theta ((n + 1) / n xi_((n))) = (n + 1) / n EE_theta xi_((n)) = (n + 1) / n theta integral_0^theta n dot (x / theta) dot (x / theta)^(n - 1) d x / theta = theta $
    Интуитивно максимум не может уменьшаться и ограничен $theta$.
    $ PP_theta (xi_((n)) <= theta - epsilon) = F^n (theta - epsilon) = ((theta - epsilon) / theta)^n = (1 - epsilon / theta)^n -> 0 $
    Значит $PP_theta (theta - epsilon < xi_((n)) <= theta) -> 1$, а это значит что $xi_((n)) ->^PP theta$
  3. Только ассимптотически несмещенная, и состоятельная
]
