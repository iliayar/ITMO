#import "../../../other/typst/lecture_mse.typ": *
#show: doc => conf(
  title: [Алгоритмы и структуры данных. Лекция 7],
  date: [24 февраля],
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
  + _Go_ ($i, "sum"$)
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

// touch: 1
