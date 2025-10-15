#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 6],
  date: [15 октября],
  number: 6,
  doc
)

#task()[]
#solution()[
  $|Omega| = binom(36, 5) quad PP = 1 / binom(36, 5)$
  $ PP(A_1 inter A_2 inter A_3 inter A_4 inter A_5) = PP(A_1) dot PP(A_2) dot dots dot PP(A_5) $
  $A_i$ независимы, т.к. выбираем сначала одно, потом другое из оставшихся.
]

#task()[]
#solution()[
  $A$ --- все числа не верны. $1 - PP(A)$.
]

#task()[]
#solution()[
  $ frac((9!)^4 dot 4!, 36!) $
  $ binom(36, 9) dot binom(27, 9) dot binom(18, 9) dot binom(9, 9) $
]

#task()[]
#solution()[
  $ (4 dot binom(13, 5)) / binom(52, 5) $
]

#task()[]
#solution()[
  Не умаляя общности $x > y > z$. $A$ --- первое болье второго, $B$ --- второе больше третьего.
  $ PP(A) = 1 / 2 quad PP(B) = 1 / 2 $
]

#task()[]
#solution()[
  $ PP(B) = 18 / 36 = 1 / 2 $
]

#task([Парадокс Монти Хола])[
  Есть три двери. Выбираем одну, открывают одну из, можно поменять выбор.
]
#solution()[
  Выбрали дверь, в ней машина с вероятностью $1/3$. Вероятность того что машина в двух других $2 / 3$, тогда после открытия одной из них вероятность "перетекает" в другую дверь, в которой машина теперь с вероятностью $2 / 3$.
]
#solution([Строгое])[
  Не умаляя общности выберем первую дверь. $A$ --- автомобиль за 2-й дверью, $B$ --- за 3-й, $C$ --- не за 1-й
  $ 
    PP(A) = PP(A inter C) = overbrace(PP(A | C), 1 / 2) dot overbrace(PP(C), 2 / 3) \
    PP(B) = PP(B inter C) = overbrace(PP(B | C), 1 / 2) dot overbrace(PP(C), 2 / 3)
  $
  После того как открыли 2-ю дверь $PP(A | C) = 1, PP(B | C) = 0$.
]
