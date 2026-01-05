#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 1],
  date: [10 сентября],
  number: 1,
  program: "ITMO MSE y2024",
  doc
)

= Время

#definition()[
  $f in cal(O)(g)$ --- $exists N med forall n >= N med f(n) <= C dot g(n)$.

  Начиная с какого места $f <= C dot g$.
]

#symb()[
  $f in cal(O)(g)$:
  - $f$ --- это $cal(O)(g)$
  - $f = cal(O)(g)$
]

#definition()[
  $f = Theta(g)$ --- $exists C_1, C_2 >= 0 med C_1 dot g(n) <= f(n) <= C_2 dot g(n)$. С точностью до $k$ $f = g$.
]

#example()[
  Пусть $f = cal(O)(g), g = Theta(h)$. $f = cal(O)(h)$.
]
#proof()[
  $ exists N_0 med forall n >= N_0 med f(n) <= C_0 dot g(n) $
  $ exists N_1 med forall n >= N_1 med C_1 h(n) <= g(n) <= C_2 h(n) $
  $ forall n >= max(N_0, N_1) med f(n) <= C_0 dot C_2 dot h(n) => f = O(h) $
]


#lemma()[
  $f = cal(O)(g) med C >= 0 => f = cal(O)(C dot g)$
]
#proof()[
$exists C_1 med f <= C_1 dot g$. $f <= frac(C_1, C) dot C dot g = C_1 dot g$.
]

= Модель памяти
#definition()[
  *RAM модель* --- все операции с числами выполняются за $cal(O)(1)$.
]

#definition()[
  *RAM-word модель* --- все операции с числами размера не больше машинного слова выполняются за $cal(O)(1)$.
]
