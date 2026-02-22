#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution[
  $ PP(F_n (x) = k / n) = PP(1/n sum_(i = 1)^n bb(1){X_i <= x} = k / n) = PP(sum_(i = 1)^n bb(1){X_i <= x} = k) $
  Заметим что $X'_i := bb(1){X_i <= x}$ имеют распределение Бернулли, а $PP(sum_(i = 1)^n X'_i = k))$ это вероятность количества успехов в схеме Бернулли. Значит
  $ PP(sum_(i = 1)^n X'_i = k) = binom(n, k) F^k (x) (1 - F(x))^(n - k) = PP(F_n (x) = k / n)  $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 2, 1))[]
#solution[
  $ F_n (x^3) = 1/n sum_(i = 1)^n bb(1){X_i <= x^3} = 1/n sum_(i = 1)^n bb(1){root(3, X_i) <= x} = F'_n (x) $
  Где $F'_n (x)$ эмпирическая функция распределения выборки $root(3, X_1), root(3, X_2), dots$.
]

#task(numbering: (..) => numbering("1.a", 2, 2))[]
#solution[
  $ F^3_n (x) = 1/n^3 (sum_(i = 1)^n bb(1) { X_i <= x })^3 = 1/n^3 sum_(i = 1)^n sum_(j = 1)^n sum_(k = 1)^n bb(1) {X_i <= x} dot bb(1) {X_j <= x} dot bb(1) { X_k <= x} = \
    = sum bb(1) {X_i <= x, X_j <= x, X_k <= x} = sum bb(1) {max(X_i, X_j, X_k) <= x} = F'_(n ^ 3) (x)
  $
  Где $F'_(n^3) (x)$ эмпирическая функция распределения выборки $X'_(i j k) := max(X_i, X_j, X_k)$:
  $ max(X_0, X_0, X_0), dots, max(X_n, X_0, X_0), max(X_0, X_1, X_0), dots, max(X_n, X_n, X_n) $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 3, 1))[]
#solution[
  Пусть $X'_i := bb(1){X_i <= x}$ --- случайные величины. Тогда если $S_n = sum X'_i$, то
  $ EE S_n / n = EE (sum X'_i) / n = (sum EE X'_i) / n = (sum F(x)) / n = F(x) quad S_n / n = F_n (x) $
  Тогда по ЗБЧ:
  $ S_n / n - EE S_n / n ->^PP 0 ==> F_n (x) - F(x) ->^PP 0 $
  Т.е. $forall epsilon > 0 med PP((F_n (x) - F(x)) < epsilon) -> 1 ==> epsilon := a med lim PP(-a < F_n - F(x) < a) = 1$
]

#task(numbering: (..) => numbering("1.a", 3, 2))[]
#solution[
  Аналогично предыдущему пункту возьмем случайные величины $X'_i$, имеющие распределение Бернулли. Значит $DD X'_i = F(x) (1 - F(x))$, $EE X'i = F(x)$. Тогда по интегральной теореме Муавра-Лапласа:
  $ PP( -a / sqrt(DD X'_i) <= (n F_n (x) - n F (x)) / sqrt(n DD X'_i) <= a / sqrt(DD X'_i)) -> Phi (a / sqrt(DD X'_i)) - Phi (-a / sqrt(DD X'_i)) \
    PP(-a <= sqrt(n) (F_n (x) - F(x)) <= a) -> 2 Phi(a / sqrt(F(x) (1 - F(x)))) - 1
  $
]
