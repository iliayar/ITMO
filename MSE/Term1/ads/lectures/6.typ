#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 6],
  date: [15 октября],
  number: 6,
  program: "ITMO MSE y2024",
  doc
)

= Count sort
#todo()
Можем сортировать пары $angle.l a_i, b_i angle.r$. Сначала отсортируем по $b$, потом еще раз по $a$. Т.к. стабильная.

= Radix sort

Сортируем $angle.l a_1, a_2, dots, a_k angle.r$. Сортируем, начиная с $a_k$. $cal(O)(k dot (n + m))$.

== Числа
Как сортировать числа с помощью этого: Запишем число в системе счисления $"BASE"$ как кортеж. Получим $cal(O)(log_("BASE") m dot (n + "BASE"))$.
#statement()[
  Выгодно брать $"BASE" approx n$. Чтобы эффективно получать $i$-ую цифру надо брать $"BASE" = 2^L$.
]

== Строки
Пусть суммарная длинна строк $sum "size" = L$. Тогда если будет сортировать по элементам, то будет работать за $cal"O"(k dot ("size" + m))$, где $m$ размер алфавита.

== Пачка массивов
Пусть хотим отсортировать несколько массивов $A_1, A_2, dots, A_s$, все элементы которых не больше $m$. Radix sort сработает за $sum (|A_i| + m)$. Как отсортировать за $sum |A_i| + m$: Сделаем большой элемент пар из элементов массива вместе с индексом массива $angle.l x, i angle.r$. Отсортируем их за $sum |A_i| + m$. Пройдемся по сортированным парам с сложим в соответсвующие места.
= Bucket sort
Разобъем числовую прямую на $n$ кусочков длины $frac("Max" - "Min" + 1, n)$. $x$ попадет в бакет $floor.l frac(x - "Min", "Max" - "Min" + 1) dot n floor.r$. Отсортируем каждый бакет:
- Insertion
- Quick sort
- Bucket sort

#theorem()[
  Если данные равномерно распределены то $E = Theta(n)$.
]
#proof()[
  $T = sum_b "size"_b^2 = sum_(i, j) ["ind"_i = "ind"_j]$, где $b$ - бакет, ind -- номер бакета.
  $ E = sum_(i, j) P ["ind"_i = "ind"_j] = $
  , где $P ["ind"_i = "ind"_j] = cases(i = j"," & 1, i != j"," & frac(1, n))$
  $ = n (n - 1) dot frac(1, n) + n = 2n - 1 $
]

= Рекурсивный перебор
#todo()
= V.E.B. (Van Emde Boas) Tree
Куча за $O(log log n)$.
#remark()[
  Что такое $O(log log n)$: Извлекаем корни, т.к. длина числа $sqrt(C) ~ frac(log C, 2)$.
]
Разбиваем диапазон чисел $[0; C]$ делим на кусочки по $sqrt{C}$. В каждом кусочке храним V.E.B $H$. Глубина $log log C$. Заведем еще V.E.B который хранит номера не пустых кусков $"ind"$. Храним также размер $"size"$ и максимальный и минимальный элемент $"min", "max"$.

#pseudocode-list()[
  - #smallcaps[ExtractMin] ()
    + $i <- floor.l "min" / sqrt(C) floor.r$
    - $H[i]$ --- Куча в которой минимум
    + *if* $H[i]."size" = 1$
      + $"ind"."ExtractMin"()$
    + *if* $H[i]."size" >= 1$
      +  $H[i]."ExtractMin"()$
    + $"size" <- "size" - 1$
    + $"min" <- H["ind"."min"]."min"$
]

#pseudocode-list()[
  - #smallcaps[Add] ($x$)
    + $i <- floor.l x / sqrt(C) floor.r$ 
    + *if* $H[i]."size" = 0$
      + $"ind"."add"(i)$
      + $H[i]."size" <- 1$
      + $H[i]."min" <- x$
      + $H[i]."max" <- x$
    + *else*
      + $H[i]."Add"(x)$
    + $"min" <- min ("min", x)$
    + $"max" <- max ("max", x)$
]
