#import "../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 8],
  date: [12 ноября],
  number: 8,
  doc
)

= Рюкзак за линию по памяти
Хотим выбрать предметы $a_i$ что $sum a_i = S$. Умеем решать за $O(n dot S)$.

#align(center, diagram(spacing: 1em, $
  "" & [i + 1, x] \
  [i, x] edge("ur", ->) edge("dr", ->) & "" \
  "" & [i + 1, x + a_i]
$))

#pseudocode-list()[
  - $"is"[0] <- 1$
  - *for* $i$
    - *for* $x$
      - *if* $"is"[x] and "is"[x + a_i] != 1$
        - $"is"[x + a_1] <- 1$
        - $p[x + a_i] <- i$
]

Сделаем за $O(frac(n dot S, w))$, где $w$ -- размер машинного слова.

#pseudocode-list()[
  - *for* $i arrow.t$
    - `is |= is << ` $a_i$
]
где `is` -- битсет

= НВП за $n log n$

Будем для каждой длины хранить конец
#pseudocode-list()[
- $"minEnd"["Length"] <- {-infinity, +infinity, +infinity, ...}$
- *for* $x in a$
  - `*upperbound(minEnd, x) = x`
]

= Деревья

- Глубина поддерева #todo()
- Максимальное независимое множество (Max-Independent-Set (Max IS))
  #definition[
    *IS* -- множество попарно несвязных вершин (нет ребра)
  ]

  Можем взять или не взять корень:
  - Если не берем, то сумма динамики по детям
  - Если берем, то сумма динамики, при том что не берем корень ребенка
  $f_(0, v)$ -- не берем корень, $f_v$ -- можем брать можем не брать
  $ f_(0, v) = sum_x f_x $
  $ f_v = max cases(sum_x f_(0, x) + 1, f_(0, v)) $

= Отрезки, Игры

- Игра на массиве: играют двое, ходят по очереди, за ход можно скушать крайнее число, нужно максимизировать сумму. Храним $f[L, R] = "Score"_1 - "Score"_2$, где $"Score"_1$ -- число очков того, кто ходит сейчас, $"Score"_2$ -- соответсвенно того кто ходит следующим.
  $ f_[L, R] = max cases(a_L - f_[L + 1, R], a_R - f_[L, R - 1]) $
- Нужно перемножить массив матриц: Перебираем последнее действие (если умноженные матрицы справа и слева).
  $ f_[0, n) = min_i f_[0, i) + f[i, n) + a_0 dot a_i dot a_n $

= Рюкзак наоборот
Считали $"maxCost"_(i, sum W )$. Если $w_i <= 10^9, S <= 10^9, "cost"_i <= 10$ то проиграем. Поэтому будет считать так $"sumW"_(i, sum "cost") -> min$. Тогда ответ на задачу: $max sum "cost"$ для $"sumW"_(n, sum "cost") <= S$.

= Маски
Множества можно кодировать числами. Пусть есть $A subset.eq {0, 1, ..., n - 1}$, тогда можно закодировать его как массив из $0, 1$. Если $n$ не очень большое ($<= 64$), то $A$ -- целое число.

== Гамильтонов путь
#definition[
  *Гамильтонов путь* -- путь, который проходит по всем вершинам ровно один раз
]

Перебор:
- Начальная вершина $v$
- Множество вершин, в которые уже заходили
Построим динамику на основе этого перебора

#pseudocode-list()[
- *for* $v$
  - $"is"_({v}, v) <- 1$
  - *for* $"mask" = 0..2^n - 1$
    - *if* $"is"_("mask", v)$
      - *for* $x in g_v$
        - *if* $x in.not "mask"$
          - $"is"_("mask" union {x}, x) <- 1$
]
Это за $O(2^n dot n^2)$, можно быстрее #todo()

= Вершинная раскраска

Найти минимальное число цветов, которым можно раскрасить граф. Переберем какие вершины покрасить в цвет 1, какие в цвет 2, и т.д. Предпосчитаем $"is"_A$ -- независимо ли множество вершин $A$.
- Пусть уже покрасили множество вершин $A$, будем хранить $k_A$ -- минимальное количество цветов.
- Выберем подможество $A$
  #pseudocode-list[
    - *for* $A$
      - $display(k_A <- min_(B subset.eq A \ "is"_B = 1) 1 + k_(A \\ B))$
  ]
  Почему $O(3^n)$: Перебираем состояние вершины $in.not A, in A and in.not B, in B$:
  ```cpp
  for (auto A = 1; A < pow(2, n); A++) {
    for (auto B = A; B > 0; B--, B &= A) {
      if (is[B]) {
        k[A] = min(k[A], 1 + k[A & ~B]);
      }
    }
  }
  ```
