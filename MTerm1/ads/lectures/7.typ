#import "../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 7],
  date: [29 октября],
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

$
f[i, "sum"] = max cases(
  f[i + 1, "sum"] quad & ,
  f[i + 1, "sum" + a_i] + "cost"_i \, quad & "if" "sum" + a_i <= S
)
$
#todo()

=== Калькулятор
Из числа $1$ получить число $N$. Можем делать:
- $x + 1$
- $2 dot x$
- $3 dot x$

Шаг $f_x = min(f_(x + 1), f_(2x), f_(3x)) + 1$, инициализация $f_n = 0, f_(> n) = + infinity$

#todo()

=== DAG (Направленный ацикличный граф)
Хотим находить пути из вершины $s$ в вершину $t$:
1. min #h(100%)
   #pseudocode-list(line-number-supplement: "Строка")[
     + $italic(F_1)$(s)
       + *if* $t = s$
         + *return* 0
       + #line-label(<dag-min-relax>) $f_1[s] <- min_(e in g[s]) italic(F_1)(e."end")  + e.w$
       + *return* $f_1[s]$
   ]
   $O(V + E)$
2. max -- то-же самое, но $max$ в @dag-min-relax
3. count -- то-же самое, но $sum$ и не учитываем $e.w$ в @dag-min-relax

=== Наибольшая возрастающая подпоследовательность

#remark[
  _Подпоследовательность_ -- помножество элементов с сохранением порядка
]

$ f_i = 1 + max_(j < i \ a_j < a_i) f_j $
Тогда ответ -- $max_(i in [0, n-1]) f_i$

=== Наибольшая общая подпоследовательность

#pseudocode-list[
  + $f[dot, dot] <- - infinity$
  + $f[0, 0] <- 0$
  + *for* $i in [0, n)$
    + *for* $j in [0, m)$
      + $"relax"(f[i + 1, j], f[i, j])$
      + $"relax"(f[i, j + 1], f[i, j])$
      + *if* $a_i = b_i$
        + $"relax"(f[i + 1, j + 1], f[i, j] + 1)$
]

#remark[
  _relax_ -- улучшить результат в смысле максимума(минимума)
  #example[
    ```cpp
    void relax(int& l, int r) {
      if (l < r) {
        l = r;
      }
    }
    ```
  ]
]

== Восстановление ответа
#todo()
