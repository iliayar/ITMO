#import "../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 7],
  date: [24 февраля],
  number: 7,
  doc
)

= Динамическое программирование
== Числа фибоначи
#todo()

== Сочетания
$ binom(n, k) = binom(n - 1, k - 1) + binom(n - 1, k) $
$ binom(n, 0) = binom(n, n) = 1 $

== Числа Каталана
$ K_n = sum_(i = 0)^(n - 1) K_i K_(n - i - 1) $
$ K_0 = 1 $

=== Subset sum
Есть массив $a$, выбрать такие элементы что $sum a_i = S$. Перебор за $O(2^n)$

#pseudocode-list()[
  + _Go_ ($i, "sum"$):
    + *if* $i = n$ *then*
      + *return*
    + #text(red)[*if* $"mem"[i, "sum"]$]
      + #text(red)[*return*]
    + #text(red)[$"mem"[i, "sum"] arrow.l 1$]
    + *if* $"sum" > 1$ *then*
      + *return*
    + _Go_ ($i + 1, "sum"$)
    + _Go_ ($i + 1, "sum" + a_i$)
]

Добавили в перебор #text(red)[мемоизацию] -- $O(n dot S)$

=== Knapsack (Рюкзак)

Выбрать такие элементы что $sum a_i <= S$ и $sum "cost"_i -> max$.
#todo()

=== Калькулятор
Из числа $1$ получить число $N$. Можем делать:
- $x + 1$
- $2 dot x$
- $3 dot x$

Шаг $f_x = min(f_(x + 1), f_(2x), f_(3x) + 1)$, инициализация $f_n = 0, f_(> n) = + infinity$
