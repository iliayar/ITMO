#import "common.typ": *

#show: doc => hw(9, doc)

#line(length: 100%)
#task()[]
#solution()[
  $ F_((xi, eta)) (x, y) = integral.double_0^1 c (x + 2y) d x d y = 3/2 c = 1 ==> c = #hl-math-answer[$2/3$] $
  $ p_xi (x) = integral_0^1 2/3 (x + 2y) d y = #hl-math-answer[$2/3 (x + 1)$] $
  $ p_eta (y) = integral_0^1 2/3 (x + 2y) d x = #hl-math-answer[$1/3 (4y + 1)$] $
  $ EE xi = integral_0^1 x p_xi (x) d x = #hl-math-answer[$5/9$] $
  $ EE eta = integral_0^1 y p_eta (y) d y = #hl-math-answer[$11/18$] $

  $ EE xi^2 = integral_0^1 x^2 p_xi (x) d x = 7/18 quad EE eta^2 = integral_0^1 y^2 p_eta (y) d y = 4/9 $
  $ DD xi = EE xi^2 - EE^2 xi = #hl-math-answer[$13 / 162$] quad DD eta = EE eta^2 - EE^2 eta = #hl-math-answer[$23 / 324$] $
  $ EE xi eta = integral_0^1 x y dot 2/3 dot (x + 2y) = 1/3 $
  $ "Cov" xi eta = EE xi eta - EE xi dot EE eta = #hl-math-answer[$- 1 / 162$] $
]

#line(length: 100%)
#task()[]
#solution()[
  Пусть такая с.в. существует. Посмотрим чему равна дисперсий с.в. $X^2$:
  $ DD X^2 = EE X^4 - EE^2 X^2 = 4 - 2^2 = 0 $
  Значит что $X^2$ принимает какое-то константное значение $c$, и тогда с.в. $X$ должна принимать значения $sqrt(c)$ или $-sqrt(c)$ соответственно с вероятностями $p$ и $1 - p$. Можем посчитать это $p$:
  $ EE X = sqrt(c) dot p - sqrt(c) (1 - p) = sqrt(c) (2p - 1) = 1 ==> 2p - 1 = 1/sqrt(c) $
  Посчитаем $c$ из $EE X^3$:
  $ EE X^3 = sqrt(c)^3 dot p - sqrt(c)^3 (1 - p) = sqrt(c)^3 (2p - 1) = sqrt(c)^2 = c = 3 $
  Проверим на $EE X^5$:
  $ EE X^5 = sqrt(3)^5 (2p - 1) = sqrt(3)^4 = 9 != 5 $
  Противоречие, значит такой с.в. *не существует*
]

#line(length: 100%)
#task()[]
#solution()[
  Для всех значений ${1, 2, 3, 4, 5}$ с.в. $X$ вероятность равна $1/6$. Посчитаем вероятности для каждого возможного значения $Y$:
  $ PP(Y = 0) = 1/2 quad PP(Y = 1) = PP(Y = 3) = dots = 0 \
    PP(Y = 2) = PP(Y = 4) = dots = PP(Y = 12)  = 1/6 dot 1/2
  $
  Посчитаем матожидания:
  $ EE X = sum_(i = 1)^6 i dot 1/6 = 7/2 quad EE X^2 = 91 / 6 $
  $ EE Y = 0 dot 1/2 + sum_(i = 1)^6 2i dot 1/12 = 7/2 quad EE Y^2 = 91 / 3 $
  $ EE X Y = sum_(i = 1)^6 i dot 0 dot 1/6 dot 1/2 + sum_(i = 1)^6 i dot 2i dot 1/6 dot 1/2 = 91 / 6  $
  И корреляцию:
  $ r(X, Y) = (EE X Y - EE X dot EE Y) / (sqrt(EE X^2 - EE^2 X) dot sqrt(EE Y^2 - EE^2 Y)) = \
    (91/6 - 7/2 dot 7 /2) / (sqrt(91 / 6 - (7/2)^2) dot sqrt(91/3 - (7/2)^2)) = 3/217 dot sqrt(217/3) dot sqrt(35/3) = sqrt(5/31) approx 0.40161
  $
]
