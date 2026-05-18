#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 9],
  date: [14 мая],
  number: 9,
  doc
)

= Гипотезы
1. Согласия. $X_1, dots, X_n ~ P$ --- со значением множества $x_1, dots, x_k$
   - Простая. $H_0: P = P_0$, т.е. $PP(X_1 = x_1) = p_1, dots, PP(X_1 = x_k) = p_k$ для набора $p_1, dots, p_x$, $sum p_i = 1, p_i >= 0$
   - Сложная. $H_0: P in {PP_theta | theta in Theta subset RR^d}$
2. Однородности
  - Критерий $chi^2$
3. 


#task(numbering: (..) => numbering("1", 2))[
  #table(
    columns: 3,
    stroke: none,
    [Число М.], $nu_i$, [],
    $0$, $476$, [],
  )
  #todo()
]

#task(numbering: (..) => numbering("1", 3))[
  Проверить что у двух выборок одинаковые распределения.
  #table(
    columns: 5,
    stroke: none,
    [], table.vline(), $x_1$, $dots$, $x_k$, table.vline(), [],
    table.hline(),
    $X$, $nu_(1,1)$, $dots$, $nu_(1,k)$, $n_1 = sum_(i = 1)^k mu_(1, i)$,
    $Y$, $nu_(2, 1)$, $dots$, $nu_(2,k)$, $n_2 = sum_(i = 1)^k mu_(2, i)$,
    $Y$, $hat(p)_i$, $dots$, $hat(p)_k$, [],
  )
  $ cases(mu_(1,i) = sum_(j = 1)^(n_1) bb(1){X_j = x_i}, mu_(2,i) = sum_(j = 1)^(n_1) bb(1){Y_j = x_i}) $
  $H_0: P_X = P_Y$. $hat(p)_i = (mu_(1, i) + mu_(2, i)) / (n_1 + n_2)$

  $ chi^2 = sum_(i = 1, dots, k \ s = 1, 2) (nu_(s, i) - n_s hat(p)_i) / (n_s hat(p)_i) = sum_(i = 1, dots, k) (nu_(1, i) - n_1 hat(p)_i) / (n_1 hat(p)_i) + sum_(i = 1, dots, k) (nu_(2, i) - n_2 hat(p)_i) / (n_2 hat(p)_i) $

  #table(
    columns: 6,
    stroke: none,
    [], [*2*], [*3*], [*4*], [*5*], [],
    [], $33$, [], [], [], [],
    [], $39$, [], [], [], [],
    [], $72$, [], [], [], [],
    $hat(p)_i$, $0.12$, $0.13$, $0.25$, $0.5$,
  )
  $ (33 - 0.12 dot 300)^2 / (0.12 dot 300) + dots approx 2.078 < 7.8 $
]
