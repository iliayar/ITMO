#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных. Часть 2],
  title: [Лекция 4],
  date: [3 марта],
  number: 4,
  program: "ITMO MSE y2025",
  doc
)

= Персистентные деревья

Храним корни всех версий
#todo()

= Невный ключ

#pseudocode-list[
  - $#smallcaps[Insert]""("Root", i, x)$
    + *if* $i < L."size"$
      + $"Root".L <- #smallcaps[Insert]""("Root".L, i, x)$
    + *else*
      + $"Root".R <- #smallcaps[Insert]""("Root".R, i - L."size" - 1, x)$
]

Итого есть операции:
- $"Insert"(i, x)$
- $"Find"(i)$
- $"Delete"(i)$

Можем сделать $"Split"$/$"Merge"$, $"Rotate"$ (циклически сдвинуть)

#todo()

= Декартово дерево

#todo()

= Splay Tree

#todo()

#theorem[
  $ "Time" = sum k_i = m $
]
