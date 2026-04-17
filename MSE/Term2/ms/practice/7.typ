#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 7],
  date: [16 апреля],
  number: 7,
  doc
)

#remark[
  До этого: $X_1, dots, X_n ~ P_theta, theta in Theta$. Теперь представим $Theta = H_0 union.sq H_1$. Проверяем $theta in H_0$ или $theta in H_1$.

  Обычно делаем предположения при $Theta = { theta_0, theta_1}$, а $H_0 = {theta_0}, H_1 = {theta_1}$.

  - Вероятность ошибки I рода: $alpha_1 = PP(H_0 | H_1)$
  - Вероятность ошибки II рода: $alpha_2 = PP(H_1 | H_0)$
]

#task[
  - $H_0$: $theta = theta_0 = 0$
  - $H_1$: $theta = theta_1 = 1$
  #table(
    columns: 3,
    table.cell(colspan: 3)[Решение],
    [], [$H_0$], [$H_1$],
    [$H_0$], [OK], [Ошибка I рода],
    [$H_1$], [Ошибка II рода], [OK],
  )
  Вероятность ошибки I рода
  $ PP_(theta_0) (X_((n)) >= 3) = 1 - PP_(theta_0)(X_1 < 3, dots, X_n < 3) = 1 - PP_(theta_0)^n (x_1 <= 3) = 1 - Phi^n (3) --> 1 $
  $ PP_(theta_1) (X_((n)) < 3) = PP_(theta_0) (X_((n)) - 1 < 2) = Phi^n (2) --> 0 $
  где $X_((n)) - 1$ --- $n$-тая порядковая сатистика распределения $cal(N)(0, 1)$. Т.к. $X_i$ при $theta_1$ имеют распределение $cal(N)(0, 1)$.
]

#task[
  1. Отвергаем $H_0$ если хотя бы одно $X_1, dots, X_n in ZZ$.
    $ PP(#[ошибка II рода]) = 0 $
    $ PP(#[ошибка I рода]) = PP(union.big {X_i in ZZ}) <= sum_(i = 0)^n underbrace(PP(X_i in ZZ), 0) = 0 $
  2. Отвергаем $H_0$ если $X_1 in ZZ$ или $X_1 in QQ$.
]

#remark[
  Полезные факты: $X_1, dots, X_n ~ cal(N)(mu, sigma^2)$, тогда $overline(X) ~ cal(N)(mu, sigma^2 / n)$
]

#task[
  $PP(overline(X) < -n^gamma) = PP(sqrt(n) dot overline(X) < -n^(0.5 + gamma)) = Phi(-n^(gamma + 0.5)) $

  При $gamma > -0.5$
]
