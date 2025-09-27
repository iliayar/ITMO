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
  $ T(n) = 1 dot T (frac(n, 2)) + n $
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
  $ T(n) = n^c dot (1 + (frac(a, b^c)) + (frac(a, b^c))^2 + dots) $
  #todo()
]

== Алгоритм Карацубы
Умножаем многочлены $A(x) dot B(x)$, где $A$, $B$ --- массивы коэффициентов.

#todo()
