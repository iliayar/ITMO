#import "common.typ": *

#show: doc => practice(
  subj: [Алгоритмы и структуры данных],
  title: [Практика 8],
  date: [6 ноября],
  number: 8,
  doc
)

#task()[]

#task()[]
#solution()[
  Упорядочим по азимумту. Убитые пираты всегда в каком-то отрезке в этом отсортированном массиве. Текущее положение можно считать всегда в одном из концов этого отрезка. Динамика по концам этого отрезка (и видимо по текщуему положению --- слева или справа).
]

#task(numbering: (..) => numbering("1.a", 3, 1))[]
#solution()[
  Динамика по поддеревьям и взяли или не взяли корень. 
]

#task(numbering: (..) => numbering("1.a", 3, 2))[]
#solution()[
  Выберем вершину, парсоч не включает одно из ее ребер. Удалим каждое, решим для дерева
]

#task(numbering: (..) => numbering("1.a", 3, 3))[]
#solution()[
  То же самое
]

#task(numbering: (..) => numbering("1.a", 4, 1))[]
#solution()[
  `n & (n - 1) == 0`
]

#task(numbering: (..) => numbering("1.a", 4, 2))[]
#solution()[
  `n && (n << 1) == ?`
]

#task(numbering: (..) => numbering("1.a", 4, 3))[]
#solution()[
  Бин поиск с маской $00 dots 0 11 dots 11$
]

#task(numbering: (..) => numbering("1.a", 4, 4))[]
#solution()[
  Аналогично
]

#task(numbering: (..) => numbering("1.a", 4, 5))[]
#solution()[
  `n ^ (n & (n - 1))`
]

#task(numbering: (..) => numbering("1.a", 4, 5))[]
#solution()[
  Ксорить половинки, пока не останется длиной $1$ --- это четность
]

#task(numbering: (..) => numbering("1.a", 5, 1))[]
#solution()[
  #pseudocode-list()[
    + $d[dot, dot] <- +infinity$
    + *for* $i in 0 dots n - 1$
      + `d[1 << i, i]` $<- 0$
    + *for* $m in 1 dots 2^n - 1$
      + *for* $v in 0 dots n - 1$
        + *if* `m & (1 << v) != 0`
          + *for* $u in 0 dots n - 1$
            + *if* `m & (1 << u) == 0`
              + `relax(d[m | (1 << u), u], d[m, v] + const(v, u))`
  ]
]

#task(numbering: (..) => numbering("1.a", 5, 1))[]
#solution()[
  Как предыдущая но инициализация `d[1, 0]` $<- 0$
]
