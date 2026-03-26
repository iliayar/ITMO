#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных. Часть 2],
  title: [Лекция 7],
  date: [24 марта],
  number: 7,
  program: "ITMO MSE y2025",
  doc
)

= Универсальное семейство

#definition[
  $cal(H) = {h}, h : U |-> M$. Если $forall x, y in U med x != y med "Pr"_(h in H) [h(x) = h(y)] <= 1 / M$.
]

= Perfect Hashing

#definition[
  $x_1, x_2, dots, x_n$. $h : [0, p) -> [0, n) med forall x_i != x_j med h(x_i) != h(x_j)$
]

#example[
  Одноуровневая. $h_1 : {x_i} |-> [0, n^2)$.
  $ "Pr" <= EE = (n (n - 1)) / 2 dot "Pr" [undershell(h(x_i) = h(x_j), 1/n^2)] <= 1/2 $
  Выбираем из семейства $M = n^2$ подходящую
]

#example[
  Двухуровенвая. $h_2 : {x_i} |-> [0, n)$
]

= Фильтр Блума

#todo()

= Кукушка
