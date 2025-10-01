#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 4],
  date: [1 октября],
  number: 4,
  doc
)

= Продолжение

$n$ ящиков, $k$ шариков

#align(center, table(
  columns: 4,
  stroke: none,
  align: center,
  gutter: 0.5em,
  [], table.vline(), [ящики \\ шарики], table.vline(), [различимы], table.vline(), [неразличимы],
  table.hline(),
  table.cell(rowspan: 3)[#rotate(-90deg, reflow: true)[различимы]] /* rotate it 90*/, [$<= 1$ шарика в ящик], [$A^k_n$], [$binom(n, k)$],
  [без ограничений], [$n^k$], [$multiset(n, k)$],
  [нет пустых ящиков], [$hat(S)(k, n)$], [$multiset(n, k - n)$],
  table.hline(),
  table.cell(rowspan: 3)[#rotate(-90deg, reflow: true)[неразличимы]], [$<= 1$ шарика в ящик], [$cases(1\, k <= n, 0\, k > n)$], [$cases(1\, k <= n, 0\, k > n)$],
  [без ограничений], [$sum_(i = 1)^n S(k, i)$], [$sum_(i = 1)^n p_i(k)$],
  [нет пустых ящиков], [$S(k, n)$], [$p_n(k)$]
))

#definition()[
  $p_k(n)$ --- количество способов разбить числа $n$  на $k$ натуральных слагаемых
  $ cases(n = n_1 + n_2 + dots + n_l, 1 <= n_1 <= n_2 <= dots <= n_k) $
]
#example()[
  $
    p_3(6) = 3 \
    1 + 1 + 4 \
    1 + 2 + 3 \
    2 + 2 + 2
  $
]

#definition()[
  *Числа Стирлинга #numbering("I", 2) рода* $S(n, k)$ --- количество способов разбить $n$ элементное множество на $k$ непустых подмножеств
]
#symb()[ $stirling(n, k)$ ]

#remark()[
    $ S(n, k) = sum_(i = 0)^(n - 1) S(n - i, k - 1) dot binom(n - 1, i) $
]

#remark()[
    $ S(n, k) = S(n - 1, k - 1) + S(n - 1, k) dot k $
]

#definition()[
  Отображением $delta$ из $X$ в $Y$ называется некое правило соответствия $forall x in X quad exists! y in T : f(x) = y$
]

#remark()[
  $|X| = n, |Y| = m$ количество отображений $m^n$.
]

#definition()[
  Отображение называется *инъективным*, если $f(x_1) = f(x_2) ==> x_1 = x_2$
]
#remark()[
  Всего инъективных отображений $A_m^n$
]
#remark()[
  Если $n > m$, то инъекций не существует (принцип Дирихле) 
]

#definition()[
  Отображение называется *сюръективным*, если $forall y in Y , exists x : f(x) = y$
]

#definition()[
  Всего сюръекций $hat(S)(n, m)$
]
#remark()[
  $k! dot S(n, k) = hat(S)(n, k)$
]

#definition()[
  Отображение называется *биективным*, если $forall y in Y, exists ! x in X : f(x) = y$ (инъекция + сюръекция)
  #todo(note: [неправильное формальное?])
]
#remark()[Всего биекций $n!$]

#theorem()[
    $ hat(S)(n, k) = sum_(i = 0)^k (-1)^(k - 1) binom(k, i) i^n $
]

#definition()[
  *Числами Белла*  называется количество способов разбить $n$-элементное множество на подмножества
]
#symb()[$B(n)$]
#remark()[
    $ B(n) = sum_(k = 1)^n S(n, k) $
]

= Формула обращения
#theorem()[
$ f_k = sum^k_(i = 0) binom(k, i) g_i <==> g_k = sum^k_(i = 0) (-1)^(k - 1)binom(k, i) f_i $, где $f_k$, $g_k$ --- числовые последовательности
]
#proof()[
  1. $quote.double==>quote.double$ Рассмотрим 
    $ 
      sum_(i = 0)^k (-1)^(k - i) binom(k, i) f_i = sum_(i = 0)^k (-1)^(k - 1) binom(k, i) sum_(j = 0)^i binom(i, j) g_j = sum_(i = 0)^k sum_(j = 0)^i (-1)^(k - i) binom(k, i) binom(i, j) g_i =  \
      = sum_(i = 0)^k sum_(j = 0)^i (-1)^(k - i) binom(k, j) binom(k - j, i - j) g_j = sum_(j = 0)^k sum_(i = j)^k (-1)^(k - i) binom(k, j) binom(k - j, i - j) g_j = \
      = sum_(j = 0)^k binom(k, j) g_j sum_(i = j)^k (-1)^(k - 1) binom(k - j, i - j) = sum_(j = 0)^k binom(k, j) g_j sum_(l = 0)^(k - j) (-1)^(k - j - l) binom(k - j, l) = #h(5em)#text(gray)[$[l = i - j]$] \
     = sum_(j = 0)^k binom(k, j) g_j sum_(l = 0)^m (-1)^(m - l) binom(m, k) dot 1^k = binom(k, k) g_j = g_j #h(5em)#text(gray)[$[m = k - j]$]
    $
]
