#import "common.typ": *

#show: doc => practice(
  subj: [Алгоритмы и структуры данных. Часть 2],
  title: [Практика 3],
  date: [24 февраля],
  number: 3,
  doc
)


#task(numbering: (..) => numbering("1", 1))[]
#solution[
  Сделаем отсортированную последовательность из дереьев, смежрим последовательности. Из этой последовательность возьмем середину в качестве корня и рекурсивно запустимся от левой и правой части. Доказываем что это AVL. $h(n) <= h(n + 1) <= h(n) + 1$.
]

#task(numbering: (..) => numbering("1", 2))[]
#solution[
  #todo()

  Назовем такую функцию которая фиксит дерево с дисбалансов в корне $B[alpha, x, beta]$.
]

#task(numbering: (..) => numbering("1", 3))[]
#solution[
  $p$ --- монотонный предикат
  #pseudocode-list[
    - $"split"(t, p)$
      + *if* $p(t."key")$
        + $chevron.l alpha, beta chevron.r <- "split"(t.l, p)$
        + *return* $chevron.l alpha, B[beta, t."key", t.r]$
      + *else*
        + $chevron.l alpha, beta chevron.r <- "split"(t.r, p)$
        + *return* $chevron.l B[t.l, t."key", alpha], beta chevron.r$
  ]
]
