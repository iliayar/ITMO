#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution[
  Т.к. проверяем на равномерное распределение, то сразу знаем вероятность каждой цифры $1/10$.
  #table(
    columns: 3,
    stroke: none,
    [Цифра], table.vline(), [Частота], table.vline(), [Вероятность],
    table.hline(),
    $0$, $74$, $1/10$,
    $1$, $92$, $1/10$,
    $2$, $83$, $1/10$,
    $3$, $79$, $1/10$,
    $4$, $80$, $1/10$,
    $5$, $73$, $1/10$,
    $6$, $77$, $1/10$,
    $7$, $75$, $1/10$,
    $8$, $76$, $1/10$,
    $9$, $91$, $1/10$,
    table.hline(stroke: 2pt),
    [], $800$,
  )
  осчитаем отклонения:
  $ sum_(i = 1)^10 (nu_i - n p_i)^2 / (n p_i) = 1/80 sum_(i = 1)^10 (nu_i - 80)^2 = 5.125 $

  При уровне значимости $alpha = 0.05$ $xi_(0.95)^2(9) approx 16.919$. $5.125 < 16.919$ значит гипотеза принимается.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Размеры выборок $n = 20$, $m = 38$. $hat(p)_i = nu_(dot, i) / (n + m)$.
  #table(
    columns: 3,
    stroke: none,
    [Ярус №1], table.vline(), [Ярус №2], table.vline(), $hat(p)_i$,
    table.hline(),
    $1$, $0$, $1/58$,
    $5$, $7$, $12/58$,
    $12$, $10$, $22/58$,
    $1$, $10$, $11/58$,
    $1$, $4$, $5/58$,
    $0$, $7$, $7/58$,
    table.hline(stroke: 2pt),
    $20$, $38$, []
  )
  $ sum_(i = 0)^k (nu_(1, i) - n hat(p)_i) / (n hat(p)_i) + sum_(i = 0)^k (nu_(2, i) - m hat(p)_i) / (m hat(p)_i) approx 13.38 $
  При $alpha = 0.05$ $xi_(0.95)^2(5) approx 11.07$. $13.38 > 11.07$ значит гипотеза о совпадении функций распределения не принимается.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution[
  Построим таблицу с частотами, где $nu_(i, j)$ --- количество человек которые ходят на пары $i$-той "стратегией" и получили зачет $j$. 
  #table(
    columns: 4,
    stroke: none,
    [], table.vline(), [Зачет], table.vline(), [Незачет], table.vline(stroke: 2pt), $nu(i, dot)$,
    table.hline(),
    [Всегда], $10$, $7$, $17$,
    [По настроению], $15$, $18$, $33$,
    [Никогда], $1$, $9$, $10$,
    table.hline(stroke: 2pt),
    $nu_(dot, i)$, $26$, $34$, $n := 60$,
  )
  Пусть $hat(p)_(i, dot) = nu_(i, dot) / n$, $hat(p)_(dot, i) = nu_(dot, i) / n$. Посчитаем
  $ sum_(i = 1)^3 sum_(j = 1)^2 (nu_(i, j) - n dot hat(p)_(i, dot) dot hat(p)_(dot, j)) / (n dot hat(p)_(i, dot) dot hat(p)_(dot, j)) approx 6.25 $
  Для $alpha = 0.05$ с $(3 - 1) dot (2 - 1) = 2$ степенями свободы $chi_(0.95)^2(2) approx 5.991 < 6.25$. Не принимаем гипотезу что посещаемость и вероятность получения зачета независимы.
]
