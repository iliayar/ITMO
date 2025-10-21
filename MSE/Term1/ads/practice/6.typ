#import "common.typ": *

// touch: 1

#show: doc => practice(
  subj: [Алгоритмы и структуры данных],
  title: [Практика 6],
  date: [16 октября],
  number: 6,
  doc
)

#task(numbering: (..) => numbering("1", 1))[]
#solution()[
  Решим для групп размером $2k + 1$. Тогда размер группы больше и меньше будет по $n dot (k + 1) / (4k + 2)$. Итоговое время:
  $ T(n) = Theta(n + n / (2k + 1) dot (2k + 1)^2) + T(n dot 1 / (2n + 1)) + T(n dot (1 - (k + 1) / (4k + 2))) $
  Нужно чтобы $1 / (2k + 1) + (3k + 1) / (4k + 2) < 1$.
  - Для $k = 1$: $1 / 3 + 4 / 6 = 1 lt.not 1$ *Не ок*
  - Для $k = 2$: $1 / 5 + 7 / 10 = 9/10 < 1$ *OK*
  - Для $k = 3$: $1 / 7 + 10 / 14 = 6/7 < 1$ *ОК*
]

#task(numbering: (..) => numbering("1", 3))[]
#solution()[
  CountSort + частичные суммы
]

#task(numbering: (..) => numbering("1.a", 4, 1))[]
#solution()[
  $max_i (max(|x_i - x^*|, |y_i - y^*|)) = max(max_i (|x_i - x^*|), max_i (|y_i - y^*|))$. Найти среднее между максимальной минимальной точкой
]

#task(numbering: (..) => numbering("1.a", 4, 2))[]
#solution()[
  Первернем систему координат (т.к. получается ромб). $x = u + v$, $y = u - v$.
  $
    |x'| + |y'| = |u' + v'| + |u' - v'| = 1 /2 max(- u' - v', u' + v') + max(-u' + v', u' - v') = \
    = 1/2 max(-u' + v + max(- u' - v', u' + v')', u' - v' + max(- u' - v', u' + v')) = \
    = max(-u' , v', -v', u') = max((-u', u'), max(-v', v')) = max(|u'|, |v'|)
  $
  Свели к предыдущей задаче заменой переменных
]

#task(numbering: (..) => numbering("1.a", 4, 2))[]
#solution()[
  $sum dots = sum_i (x_i - x^*)^2 + sum_i (y_i - y^*)$ --- каждое слагаемое это полином второй степени по $x^*$ ($y^*$). Найдем производную:
  $ sum_i - 2x_i + 2x^* = 0 ==> x^* = 1/n sum_i x_i $
]

#task(numbering: (..) => numbering("1.a", 4, 3))[]
#solution()[
  Аналогично $f = sum_i |x_i - x^*| -> min$ --- это ломанная парабола. При $x -> x + epsilon: f -> f + l dot epsilon - r dot epsilon -> min$.
]

#task(numbering: (..) => numbering("1.a", 5, 1))[]
#solution()[По символу с конца]

#task(numbering: (..) => numbering("1.a", 6, 2))[]
#solution()[Построенние суффиксоного массива для циклических сдвигов]
