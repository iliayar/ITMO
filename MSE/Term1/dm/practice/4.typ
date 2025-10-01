#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 4],
  date: [1 октября],
  number: 4,
  doc
)

#task(numbering: (_, n) => n)[#todo()]

#task(numbering: (_, n) => n)[
  $ k^n = sum_(i = 0)^k binom(k, i) hat(S)(n, i) $
  Каждое слагаемое --- все возможные сюръекции для фиксированного $i$.
  $ hat(S)(n, k) = sum_(i = 0)^k (-1)^(k - i) binom(k, i) i^n $
]

#task(numbering: (_, n) => n)[
  Посчитаем по разрядам: в каждом разряде сумма будет $3! (1 + 2 + 3 + 4) dot 10^k$, где $k$ --- номер разряда.
  $ 6 dot 10 + 6 dot 10^1 + 6 dot 10^2 + 6 dot 10^3 + 6 dot 10^4 = 66660 $ 
]

#task(numbering: (_, n) => n)[#todo()]

#task(numbering: (_, n) => n)[
]

#task(numbering: (_, n) => n)[
  - $S(n, 1) = 1$ --- $1$ множество из $n$ элементов
  - $S(n, n) = 1$ --- множества из $1$ элемента, порядок не важен
  - $S(n, 2) = frac(hat(S)(n, 2), 2!)$ --- наберем первое множество, второе получим автоматически, что-то посчитаем два раза
    $ S(n, 2) = frac(sum_(i = 1)^(n - 1) binom(n, i), 2!) = frac(2^n - 2, 2!)$
  - $S(n, n - 1) = binom(n, 2)$ --- одно двухэлементное множество, остальные по одному
]

#remark()[
  $ 2^n = (1 + 1)^n = sum_(i = 0)^n binom(n, i) $
]

#remark()[
  - $S(0, 0) = 1, S(n, 0) = 0$
  - $S(j, k) = 0, k > j$
]

#task(numbering: (_, n) => n)[
  Выбираем подмножество размера $k$ и разбиваем его на подмножества, все остальное идет в отдельное множество.
]
