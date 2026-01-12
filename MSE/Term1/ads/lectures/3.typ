#import "/other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 3],
  date: [24 сентября],
  number: 3,
  program: "ITMO MSE y2024",
  doc
)

= Разделяй и Властвуй

== Merge Sort
#todo()

Время работы этой сортировки:
$ T(n) = 2 dot T (frac(n, 2)) + n $
Посмотрим на дерево рекурсии: каждый раз размер задачи уменьшается в $2$ раза. Всего "уровней" $log n$, на каждом уровне ровно $n$. $T(n) = n log n$. 

#remark()[
  Чтобы не было проблем с округлением можно "зажать" $n$ между степенями двойки $2^(k - 1) <= n <= 2^k$ в данном случае.
]
#remark()[
  Можно сказать что один рекурсивный вызов от $x$ а другой за $n - x$, так тоже можно избавиться от проблем с округлением. 
]

== Бинарный поиск
#todo()

== Мастер Теорема

#example()[
  $ T(n) = w dot T (frac(n, 2)) + n $
  Количество слоев также $log n$, но на каждом слое теперь не $n$, а убывающая геометрическая прогрессия:
  $ n (1 + frac(1, 2) + frac(1, 4) + dots ) = Theta(1) $
]

#remark()[
  $ 1 + alpha + alpha^2 + dots + alpha^k = frac(alpha^(k + 1) - 1, alpha - 1) = Theta(alpha^k) $
]

#example()[
  $ T(n) = 3 dot T (frac(n, 2)) + n $
  Слоев столько же, но каждом слое теперь $frac(3, 2) n$
  $ n (1 + frac(3,2) + (frac(3,2))^2 + dots) = Theta(n dot (frac(3, 2))^(log n)) = Theta(3^(log n)) = Theta(n^(log 3)) $
]

#theorem("Мастер теорема")[
  $T(n) = a dot T(frac(n, b)) + n^c$, где $a > 0, b > 1, c >= 0$. Тогда:
  1. $a = b^c ==> T(n) = Theta(n^c dot log n)$
  2. $a < b^c ==> T(n) = Theta(n^c)$
  3. $a > b^c ==> T(n) = Theta(n^(log_b a))$
]
#proof()[
  $ T(n) = n^c dot (1 + (frac(a, b^c)) + (frac(a, b^c))^2 + dots) = n^c sum_(i=0)^(log n) (a / b^c)^i $
  1. $a / b^c = 1 ==> T(n) = Theta(n^c log n)$
  2. $a / b^c < 1 ==> T(n) = Theta(n^c)$, т.к. $sum^infinity alpha^i = "const"$, т.к. при $alpha < 1$ ряд сходится.
  3. $a/ b^c > 1$. Сумма равна $1 + alpha + alpha^2 + dots = (alpha^(k + 1) - 1) / alpha ~ a^k $. Значит :
  $ T(n) ~ n^c (a / b^c)^(log_b n) = n^c (a^(log_b n) / undershell((b^(c dot log_b n)), n^c)) = n^(log_b a) $
]

== Алгоритм Карацубы
Умножаем многочлены $A(x) dot B(x)$, где $A$, $B$ --- массивы коэффициентов. н.у.о $n = 2^k$.

Разделим массив $A$ на два $A_1$ и $A_2$. Тогда $A(x) = A_1(x) + x^(n / 2) A_2(x)$

$ A dot B = (A_1 + x^(n / 2) A_2) dot (B_1 + x^(n / 2) B_2) = A_1 dot B_1 + x^(n / 2) (A_1 B_2 + A_2 B_1) + x^n A_2 B_2 $
Сложения и сдвиги массивов умеем за линию. Тогда $T(n) = 4 T(n / 2) + n = O(n^2)$. Заметим что
$ A_1 B_2 + B_2 A_1 = (A_1 + A_2) (B_1 + B_2) - A_1 B_1 - A_2 B_2 $
Получается нужно посчитать только $A_1 B_1$, $A_2 B_2, (A_1 + A_2) (B_1 + B_2)$. Тогда $T(n) = 3 T(n / 2) + n = O(n^(log_2 3))$
