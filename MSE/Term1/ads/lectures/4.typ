#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 4],
  date: [1 октября],
  number: 4,
  program: "ITMO MSE y2024",
  doc
)

= Нижние оценки
#statement()[
  $forall$ сортировка на $<$ $Omega(n log n)$
]
#proof()[
  Пусть делаем $<= k$ сравнений. Корректная сортировка сортирует как минимум все перестановки, которых $n!$.
  Докажем что $2^k >= n!$: Сравнение возвращает 1 бит информации (меньше или больше или равно).
  Пусть сортировка всегда делает $k$ операций. В результате получилось $k$ результатов сравнения ($k$ бит).
  Пусть $2^k < n!$, тогда $exists p != q$, ($p, q$ -- перестановки), т.е. у них одинаковые результаты сравнения, значит алгоритм делал одни и те же действия, значит одна из не будет отсортирована. Значит $2^k >= n! => k => log n!$.
]

= Сортировки
- Insertion Sort. Работает за $cal(O)(n + I)$, где $I$ --- количество инверсий.
- Selection Sort. Делает всего лишь $O(n)$ swap'ов.
#todo()

= Кучи
== Бинарная
#todo()
Построение за $O(n)$ -- делаем `SiftDown(i)` для $i colon.eq n dots 1$.
== d-Куча
#todo()
Вместо двух детей, $d$ детей
- #smallcaps[SiftUp] $cal(O)(log_d n)$
- #smallcaps[SiftDown] $cal(O)(d log_d n)$
- #smallcaps[Insert] $cal(O)(log_d n)$
- #smallcaps[ExtractMin] $cal(O)(d log_d n)$
- #smallcaps[BuildHeap] $cal(O)(n)$
  $ T(n) = sum_(k = 1)^h d k d^(h - k) = d dot d ^h sum_(k = 1)^h k / d^k ~ d n sum_(k = 1)^h k / d^k $
  $ A = sum_(k = 1)^infinity k / d^k quad B = sum_(k = 1)^infinity 1 / d^k = 1 / d (1 / (1 - 1/d)) = 1/(d - 1) $
  $ A - B = sum_(k = 2)^infinity = 1/d sum_(k = 1)^infinity k / d^k = 1/d A ==> A - 1/(d - 1) = 1/d A ==> A = d / (d - 1)^2 $
  $ T(n) = (d / (d - 1))^2 <= 4 n $
== Skew Heap
Есть операция `Merge` (Meld), которая объединяет две кучи.
- `Add` -- сделать `Merge` с кучей из одного элемента
- `ExtractMin` -- Удалить корень, сделать `Merge` на его детях


#pseudocode-list("Merge")[
  - #smallcaps[Merge] ($A, B$)
    + *if* $A."value" >= B."value"$
      + $A."right" <- "Merge"(A."right", B)$
      + $"Swap"(A."right", A."left")$ --- Для балансировки
    + *else*
      + $B."right" <- "Merge"(A, B."right")$
      + $"Swap"(B."right", B."left")$
]
