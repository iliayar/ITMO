#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution[
  $T_n = overline(X)$.
  $ EE_lambda T_n = EE X_i = lambda quad DD_lambda T_n = 1 / n^2 dot n DD X_i = lambda / n $
  По ЦПТ:
  $ (T_n - lambda) dot sqrt(n / lambda) ->^d cal(N)(0, 1) $
  А также введем $xi_n := sqrt(n) (T_n - lambda) -> cal(N)(0, lambda)$. И $eta_n := sqrt(T_n) -> sqrt(lambda)$ по ЗБЧ. Тогда по лемме Слуцкого:
  $ (sqrt(n) (T_n - lambda)) / sqrt(T_n) -> (sqrt(n) (T_n - lambda)) / sqrt(lambda) $
  $ PP_lambda (z_(epsilon / 2) <= (sqrt(n) (T_n - lambda)) / sqrt(lambda) <= z_(1 - epsilon / 2)) -> 1 - epsilon ==> PP_lambda (z_(epsilon / 2) <= (sqrt(n) (T_n - lambda)) / sqrt(T_n) <= z_(1 - epsilon / 2)) -> 1 - epsilon $
  $ PP_lambda (z_(epsilon / 2) <= (sqrt(n) (T_n - lambda)) / sqrt(T_n) <= z_(1 - epsilon / 2)) = PP_lambda ((sqrt(T_n) z_(epsilon /2)) / sqrt(n) <= T_n - lambda <= (sqrt(T_n) z_(1 - epsilon /2)) / sqrt(n)) = \
    = PP_lambda ((sqrt(T_n) z_(epsilon /2)) / sqrt(n) <= - T_n + lambda <= (sqrt(T_n) z_(1 - epsilon /2)) / sqrt(n)) = PP_lambda ((sqrt(T_n) z_(epsilon /2)) / sqrt(n) + T_n <= lambda <= (sqrt(T_n) z_(1 - epsilon /2)) / sqrt(n) + T_n) -> 1 - epsilon
  $

]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Хотим найти функцию распределения $X' = (n (theta - X_((n)))) / theta$:
  $ F_(X')(t) = PP((n (theta - X_((n)))) / theta < t) = PP(X_((n)) > theta - (theta t) / n) = 1 - PP(X_((n)) <= theta - (theta t) / n) = \
    = 1 - product_i^n PP(X_i <= theta - (theta t) / n)
  $
  Т.к. $X_i$ одинаково распределенные и для них известна функция распределения $F_(X_i) (t) = t / theta$, то
  $ F_(X')(t) = 1 - PP(X_1 <= theta - (theta t) / n)^n = 1 - (1 - t / n)^n ->_(n -> +infinity) 1 - e^(-t) $
  Можно также заметить что функция распределения $"Exp"(1)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution[
  Возьмем $X' ~ "Exp"(1)$ из предыдущей задачи. Известно что квантили для это распределения#footnote[`https://en.wikipedia.org/wiki/Exponential_distribution#Quantiles`] $z_p = - ln (1 - p)$. Тогда можем построить доверительный интервал:
  $ PP(z_(epsilon / 2) < X' < z_(1 - epsilon / 2)) = PP(z_(epsilon / 2) < (n (theta - X_((n)))) / theta < z_(1 - epsilon / 2)) = PP(z_(epsilon / 2) < n - n/theta X_((n)) < z_(1 - epsilon / 2)) = \
    = PP(1 / (n - z_(epsilon / 2)) < theta / (n X_((n))) < 1 / (n - z_(1 - epsilon / 2))) = PP((n X_((n))) / (n - z_(epsilon / 2)) < theta < (n X_((n))) / (n - z_(1 - epsilon / 2))) -> 1 - epsilon
  $
]
