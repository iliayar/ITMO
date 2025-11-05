#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 9],
  date: [5 ноября],
  number: 9,
  doc
)

#task()[]
#solution()[
  $ F_((xi, eta)) (x, y) = integral.double_(R^2) 1 / (1 + x^2 + y^2 + x^2 y^2) d x d y = 1 = $
  $ = integral_R 1 / (1 + y^2) integral_R 1 / (1 + x^2) d x d y = integral_R lr(1 / (1 + y^2) arctan x |)_R = dots = c pi^2 $
]

#solution()[
  $ p_xi (x) = integral_R 1 / (pi^2 (1 + x^2 + y^2 + x^2 y^2)) d y = 1 / (pi^2 (x^2 + 1)) integral_R 1 / (1 + y^2) d y = 1 / (pi (x^2 + 1)) $
]
#solution()[
  $ p_eta (y) = dots = 1 / (pi (1 + y^2)) $
]

#task()[]
#solution()[
  Т.к. равномерно распределено, то плотность --- константа.
  $ integral.double_(|x| + |y| <= 1) c d x d y = 1 = c dot integral.double_(|x| + |y| <= 1) 1 d x d y = c dot 2 ==> c = 1/2 $
  $ p_xi (x) = integral_(-1 + |x|)^(1 - |x|) 1/2 d y = 1 - |x| $
  $ p_xi (x) = cases(
      1 - |x| quad & "," -1 <= x <= 1,
      0 quad & "," #text[иначе]
  ) $
]
#solution()[
  $ p_eta (y) = dots = 1 - |y| $
]
#solution()[
  не независимы? #todo()
]

#definition()[
  Коэффициент кореляции
  $ "Cov" (X, Y) = EE (X Y)  - EE X dot EE Y $
  $ r_(x, y) = ("Cov" (X, Y)) / (sqrt(DD x) dot sqrt(DD y)) = (EE (X Y) - EE X dot EE Y) / (sqrt(EE X^2 - EE^2 X) dot sqrt(EE Y^2 - EE^2 Y)) $
]

#task()[]
#solution()[
  Вероятности вытащить выигрышный и нет у обоих одинаковая: $1/3$ и $2/3$. Вытягивают по одному билету всего, т.е. $xi, eta$ либо $0$ либо $1$.
  $ EE X = EE Y = 0 dot 2/3  + 1 dot 1/3 = 1/3 quad EE X^2 = EE Y^2 = 1/3 $
  $ EE X Y = 1 dot 1 dot 1/3 dot 1/3 $
]

#task()[]
#solution()[
  $ p_xi (x) = integral_0^1 x + y d y = x + 1/2 quad p_eta (y) = integral_0^1 x + y d x = y + 1/2 $
  $ EE xi = integral_0^1 x p_xi d x = integral_0^1 x (x + 1/2) d x = 7/12 $
  $ EE xi^2 = integral_0^1 x^2 p_xi d x = integral_0^1 x^2 ( x + 1/2 ) d x = 5/12 $
  $ DD xi = EE xi^2 - EE^2 xi = 5/12 - (7/12)^2 = 11/144 $
  $ EE xi eta = integral_0^1 integral_0^1 x y ( x + y) d x d y $
  $ EE xi eta = integral_0^1 integral_0^1 dots = 1/3 $
]
