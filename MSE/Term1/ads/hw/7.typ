#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution()[
  Для начала составим рекурентную формулу для вычисления вероятности выпадения $m$ орлов из первых $j$ монет:
  $ f_(m, j) = f_(m, j - 1) dot (1 - p_j) + f_(m - 1, j - 1) dot p_j $
  Либо до этого выпало $m$ орлов и $j$-ая монета не орел, либо до этого выпало $m - 1$ орлов и $j$-ая монета орел. И $f_(0, 0)$ можно считать равным $1$, т.к. из $0$ монет всегда будет выпадать $0$ орлов.

  Можно либо посчитать динамику в виде таблицы $k times j$, либо мемоизировать:
  #pseudocode-list()[
    - $f(m, j)$:
      + *if* $m = 0 and j = 0$
        + *return* $1$
      + *if* $exists "mem"_(m, j)$
        + *return* $"mem"_(m, j)$
      + $"res" <- f(m, j - 1) + f(m - 1, j - 1)$
      + $"mem"_(m, j) <- "res"$
      + *return* $"res"$
  ]
  Каждое $f(m, j)$ будет посчитано ровно один раз. Ищем $f(k, n)$ и используем только меньшие $m$, $j$, значить всего таких $f(m, j)$ будет $k dot n$. Значит время работы $cal(O)(n dot k)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution()[
  Заметим что если суффиксы $s_(n - i)dots s_n$ и $s_(n - j) dots s_n$ имеют некий общий префикс $s_(n - i) dots s_(n - i + m) = s_(n - j) dots s_(n - j + m)$ то если $s_(n - i - 1) = s_(n - j - 1)$ тогда общий префикс суффиксов $i + 1$ и $j + 1$ будет на $1$ длинее. Иначе если $s_(n - i - 1) != s_(n - j - 1)$, то у эти суффиксов $i + 1$ и $j + 1$ уже не может быть общего префикса, т.к. первый символ уже различается. Тогда получается что длину общего префикса можно посчитать так:
  $ f_(i, j) = cases(
    1 + f_(i - 1, j - 1) quad & "," s_(n - i) = s_(n - j),
    0                         & "," #text[иначе]
  ) $
  Понятно что это будет длина максимального префикса, т.к. если бы это было не так, то значит существует более длинный префикс и какое-то $m$ и символ $s_(n - i + m) = s_(n - j + m)$, который не входит в $f_(i, j)$, но по определению $f_(i, j)$ он должен входить в $f_(i - m, j - m)$, а значит должен входить и в $f_(i - m + 1, j - m + 1)$ и тд. до $f_(i - m + m, j - m + m) = f_(i, j)$.

  Тогда можем посчитать динамику $f_(i, j)$ где $f_(i, j) = 0$ для $i <= 0$ или $j <= 0$, остальные по формуле выше. Это и будет ответом.
  #pseudocode-list()[
    - $forall i <= 0, j <= 0: f_(i, j) <- 0$
    + *for* $i := 1 dots n$
      + *for* $j := 1 dots n$
        + *if* $s_(n - i) = s_(n - j)$
          + $f_(i, j) <- 1 + f_(i - 1, j - 1)$
        + *else*
          + $f_(i, j) <- 0$
  ]
  Итоговая сложность $cal(O)(n^2)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 3, 1))[]
#solution()[
  Будем считать $f_i$ --- минимальная длина закодированного суффикса строки $s_i dots s_n$. Тогда $f_(i - 1)$ это одно из:
  2. Это начало повторения какого-то франмента строки начиная с символа $j < i$ длины $k$: $s_j dots s_(j + k) = s_i dots s_(i + k)$. Тогда это суффикс $s_(i + k)$ с правилом $(k, j)$.
  1. Суффикс $i$ с символом $s_i$.
  Т.к. других способов записать суффикс нет, то минимальная из всех возвожных записей выше и будет минимальной.

  Чтобы восстановить ответ будет запоминать какой из двух вариантов выше и с какими параметрами применили:
  #pseudocode-list()[
    - #smallcaps[RuleLength]$(k, i)$ --- возвращает длину строки, соответствующей правилу $(k, i)$.
    - $"ans"_i$ --- как получили закодированный суффикс $i$
    - $f_i <- infinity$
    - $f_(n + 1) <- 0$
    + *for* $i := n dots 1$
      + *for* $j := 1 dots (i - 1)$    
        + *for* $k := 1 dots n - i$
          + *if* $s_(i + k) != s_(j + k)$
            + *break*
          + *if* $f_(i + k) +$ #smallcaps[RuleLength]$(k, j) < f_i$:
            + $f_i <- f_(i + k) +$ #smallcaps[RuleLength]$(k, j)$
            + $"ans"_i <- angle.l "rule", k, j angle.r$
      + *if* $f_(i + 1) + 1 < f_i$
        + $f_i <- f_(i + 1)$
        + $"ans"_i <- angle.l "raw" angle.r$
  ]

  Ответ восстановим из массива $"ans"$:
  #pseudocode-list()[
    - $s_e$ --- закодированная строка 
    + $i <- 1$
    + *while* $i <= n$
      + *if* $angle.l "rule", k, j angle.r := "ans"_i$
        + $s_e <- s_e + \"(k, j)\"$
        + $i <- i + k$
      + *else if* $angle.l "raw" angle.r := "ans"_i$
        + $s_e <- s_e + s_i$
        + $i <- i + 1$
  ]

  Итоговая сложность $cal(O)(n^3)$ --- три вложенных цикла по $<= n$.
]

#task(numbering: (..) => numbering("1.a", 3, 2))[]
#solution()[
  Для начала заметим что $f_i > f_j$ при $i < j$, т.к. минимальная длина суффикса всегда строго увеличивается. Тогда значит что при константном #smallcaps[RuleLength]$(k, j) = "RL"$ в цикле по $k$ всегда $f_i + "RL" > f_(i + 1) + "RL"$. А это значит что достаточно взять такое максимально $k$ что $s_(i + k) = s_(j + k)$. Это в точности длина максимального префикса суффиксов $i$ и $j$, которую можно предпосчитать (как известно из предыдущей задачи за $cal(O)(n^2)$). В остально алоритм такой-же:
  #pseudocode-list()[
    - $"maxPrefix"_(i, j)$ --- предпосчитанные максимальные префиксы
    - $"ans"_i$ --- как получили закодированный суффикс $i$
    - $f_i <- infinity$
    - $f_(n + 1) <- 0$
    + *for* $i := n dots 1$
      + *for* $j := 1 dots (i - 1)$    
        + $k <- "maxPrefix"_(i, j)$
        + *if* $k != 0 and f_(i + k) + "RL" < f_i$:
          + $f_i <- f_(i + k) + "RL"$
          + $"ans"_i <- angle.l "rule", k, j angle.r$
      + *if* $f_(i + 1) + 1 < f_i$
        + $f_i <- f_(i + 1)$
        + $"ans"_i <- angle.l "raw" angle.r$
  ]

  Итоговая сложность $cal(O)(n^2)$ на предпосчет $"maxPrefix"$ и два вложенных цикла по $<= n$, получается $cal(O)(n^2)$.
]

#task(numbering: (..) => numbering("1.a", 3, 3))[]
#solution()[
  #todo()
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 4, 1))[]
#solution()[
  $ b_i = max_(0 <= j <= min(k, i)) (a_(i - j) + v dot j) = max_(0 <= j <= min(k, i)) (a_(i - j) - v dot (i - j) + v dot i) = \
    = max_(max(0, i - k) <= j <= i) (a_j - v dot j) + v dot i
  $

  Построим массив $a'$, такой что $a'_i = a_i - v dot i$. Пройдемся по нему с окном размеров $k$, поддерживая очередь с максимумом, из которой можем получать максимум в окне за $cal(O)(1)$. Построим массив $b_i$ из этих максимумов $+ v dot i$. Тогда элементы $b_i$ будут в точности:
  $ b_i = max_(max(0, i - k) <= j <= i) a'_j + v dot i = max_(0 <= j <= min(k, i)) (a_(i - j) + v dot j) $
  Итоговая сложность $cal(O)(n)$.
]

#task(numbering: (..) => numbering("1.a", 4, 2))[]
#solution()[
  Модифицируем рюкзак, добавив возможность брать несколько:
  $ f_(i + 1, s) = max cases(
    f_(i, s),
    max_(0 <= j <= k_i) f_(i, s - w_i dot j) + v_i dot j
  ) = max_(0 <= j <= k_i) f_(i, s - w_i dot j) + v_i dot j $
  Обозначим за $f'_(i, s_r, s_d) := f_(i, s_d dot w_i + s_r)$.
  $ f_(i, s - w_i dot j) = f_(i, (s div w_i - j) dot w_i + (s mod w_i)) $
  Тогда по аналогии с предыдущим пунктом преобразуем второе выржение:
  $ max_(0 <= j <= k_i) f_(i, s - w_i dot j) + v_i dot j = max_(0 <= j <= k_i) f'_(i, s mod w_i, s div w_i - j) + v_i dot j = \
    = max_(0 <= j <= k_i) f'_(i, s mod w_i, s div w_i - j) - v_i dot (s div w_i - j) + v_i dot (s div w_i) = \
    = max_(s div w_i - k_i <= j <= s div w_i) (f'_(i, s mod w_i, j) - v_i dot j) + v_i dot (s div w_i) = \
    = max_(s div w_i - k_i <= j <= s div w_i) (f_(i, j dot w_i + s mod w_i) - v_i dot j) + v_i dot (s div w_i)
  $
  Видно что для каждого $f_(i, s)$ внутри максимума$s mod w_i$ фиксировано, т.е. идем по $s'$ с одинаковым остатком. Чтобы быстро находить такие максимумы в окне можем поддерживать $w_i$ очередей с максимумом. Заметим также что ищем максимум по $f_(i, j dot w_i + s mod w_i) - v_i dot j$ что при неком $s'$ таком что $s' = j dot w_i + s mod w_i$ (т.е. $s' div w_i = j$) можно записать как $f_(i, s') - v_i dot (s' div w_i)$. Т.е. будем считать в очередях максимум по $ f_(i, s) - v_i dot (s div w_i)$. Тогда в итоге считаем такую динамику

  $ f_(i + 1, s) = max_(max(s div w_i - k_i, 0) <= j <= s div w_i) (f_(i, j dot w_i + s mod w_i) - v_i dot j) + v_i dot (s div w_i) $

  При том что максимум можно достать из соответствующей остатку $s mod w_i$ очереди за $cal(O)(1)$.

  // TODO(iliayar): Move this fix to main?
  #show smallcaps: set text(font: "linux libertine")

  #pseudocode-list()[
    - $q_i$ --- очереди с максимумом
    - $f_(i, s)$ --- динамика
    + $f_(i, s) <- infinity$
    + $f_(0, s) <- 0$
    + *for* $i := 0 dots n - 1$
      + *for* $s := 0 dots W$
        + $q_(s mod w_i).$#smallcaps[Push]$(f_(i, s) - v_i dot (s div w_i))$
        + $q_(s mod w_i).$#smallcaps[Pop]$(f_(i, s - (k_i - 1) dot w_i) - v_i dot (s div w_i))$ --- удаляем элемент не входящий в окно
        + $f_(i + 1, s) <- q_(s mod w_i).#smallcaps("Max")"()" + v_i dot (s div w_i)$
      + $forall i: q_i.#smallcaps("Clear")"()"$
  ]
  Получается итоговая сложность $cal(O)(n W)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 5))[]
#solution()[
  Пусть $f_(i, a, b)$ --- что можно набрать первому на сумму $a$, второму на сумму $b$ а третьему соответствено на сумму $sum_i v_i - a - b$. Тогда можем посчитать динамику:
  $ f_(i + 1, a, b) = f_(i, a - v_i, b) or f_(i, a, b - v_i) or f_(i, a, b) $
  Соответственно можем отдать подарок первому второму или третьему. Проще написать с динамикой вперед:
  #pseudocode-list()[
    - $f_(i, a, b)$ --- динамика
    + $f_(0, a, b) <- "false"$
    + $f_(0, 0, 0) <- "true"$
    + *for* $i := 0 dots n - 1$
      + *for* $a := 0 dots W$
        + *for* $b := 0 dots W$
          + $f_(i + 1, a + v_i, b) <- f_(i, a, b) or f_(i + 1, a + v_i, b)$
          + $f_(i + 1, a, b + v_i) <- f_(i, a, b) or f_(i + 1, a, b + v_i)$
          + $f_(i + 1, a, b) <-  f_(i, a, b) or f_(i + 1, a, b)$
  ]
  Чтобы найти ответ пройдемся по всем $f_(n, a, b)$ и найдем минимальную разность.
  #pseudocode-list()[
    - $m <- infinity$
    - $a_m, b_m$
    + $S = sum_i^n v_i$
    + *for* $a := 0 dots W$
      + *for* $b := 0 dots W$
        + *if* $not f_(n, a, b)$
          + *continue*
        + $d <- max(a, b, S - a - b) - min(a, b, S - a - b)$
        + *if* $d < m$
          + $m <- d$
          + $a_m <- a$
          + $b_m <- b$
  ]
  Для восстановления ответа пройдем по динамике обратно начиная с $f_(n, a_m, b_m)$ по таким $a, b$ что $f_(i, a, b) = "true"$:
  #pseudocode-list()[
    - $p_i$ --- подарки
    - $a_m, b_m$ --- ответ
    + $a <- a_m$
    + $b <- b_m$
    + *for* $i := n dots 1$
      + *if* $f_(i - 1, a, b)$
        + $p_2 <- p_2 union {i - 1}$
      + *else if* $f_(i - 1, a, b - v_i)$
        + $p_1 <- p_1 union {i - 1}$
        + $b <- b - v_i$
      + *else if* $f_(i - 1, a - v_i, b)$
        + $p_0 <- p_0 union {i - 1}$
        + $a <- a - v_i$
  ]

  Такой обратный путь обязан существовать, т.к. иначе $f_(n, a_m, b_m)$ не могло быть равно $"true"$. В $p$ будет распределение подарков. Общая сложность $cal(O)(n W^2)$ --- три вложенных цикла для подсчета динамики.
]
