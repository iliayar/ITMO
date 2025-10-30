#import "common.typ": *

#show: doc => hw(8, doc)

#line(length: 100%)
#task()[]
#solution()[
  Посчитаем сначала вероятность попасть ровно $k$ из $3$-х раз:
  $ PP(S_n = k) = binom(3, k) 0.8^k dot 0.2^(3 - k) $
  И тогда функция распределения:
  $ F(x) = cases(
    0 quad & "," x < 0,
    PP(S_n = 0) quad & "," 0 <= x < 1,
    PP(S_n in {0, 1}) quad & "," 1 <= x < 2,
    PP(S_n in {0, 1, 2}) quad & "," 2 <= x < 3,
    1 quad & "," x >= 3,
  ) = #hl-math-answer[$cases(
    0 quad & "," x < 0,
    0.008 quad & "," 0 <= x < 1,
    0.104 quad & "," 1 <= x < 2,
    0.488 quad & "," 2 <= x < 3,
    1 quad & "," x >= 3,
  )$] $
]

#line(length: 100%)
#task()[]
#solution()[
  Для честной игральной кости $forall x in {1, 6} : p(x) = 1/6$. Тогда можем сразу посчитать матожидание:
  $ EE X = sum_(i = 1)^6 i dot 1/6 = #hl-math-answer[$7/2$] quad EE X^2 = sum_(i = 1)^6 i^2 dot 1/6 = 91 / 6 $
  И дисперсию:
  $ DD X =  EE X^2 - EE^2 X = #hl-math-answer[$35/12$]$
]

#line(length: 100%)
#task()[]
#solution()[
  $ integral_(-infinity)^(+infinity) f(x) d x = integral_1^5 a (x - 1)^2 d x = lr(a dot (x - 1)^3/3 |)_1^5 = 64/3 dot a = 1 ==> #hl-math-answer[$a = 3 / 64$] $
  $ PP(3 <= X < 4) = PP(X < 4) - PP(X < 3) = F(4) - F(3) = \
    = integral_1^4 3/64 (x - 1)^2 d x - integral_1^3 3/64 (x - 1)^2 d x = #hl-math-answer[$19 / 64$]
  $
]

#line(length: 100%)
#task()[]
#solution()[
  $ F'(x) = integral_(-infinity)^x f(t) d t = integral_2^x 2t - 4 d t = lr(2t^2 / 2 - 4t|)_2^x = x^2 - 4x + 4 $
  $ F(x) = #hl-math-answer[$cases(
    0 quad & "," x < 2,
    x^2 - 4x + 4 quad & "," 2 <= x <= 3,
    1 quad & "," x > 3
  )$] $
  $ PP(2.5 < X < 3.5) = PP(X < 3.5) - PP(X <= 2.5) = PP(X <= 3) - PP(X <= 2.5) = \
    = F(3) - F(2.5) = #hl-math-answer[$0.75$]
  $
  $ EE X = integral_2^3 x dot (2x - 4) d x = #hl-math-answer[$8/3$] $
  $ EE X^2 = integral_2^3 x^2 dot (2x - 4) d x = 43/6 $
  $ DD X = EE X^2 - EE^2 X = #hl-math-answer[$1/18$] $

]

#line(length: 100%)
#task()[]
#solution()[
  Для жетона $p_1(0) = p_1(2) = 1/2$, для кубика $p_2(1) = p_2(2) = p_2(3) = 1/3$. Тогда можем посчитать вероятность для каждой суммы:
  $ PP(S=1) = p_1(0) dot p_2(1) = 1/6 quad PP(S=2) = p_1(0) dot p_2(2) = 1/6 $
  $ PP(S=3) = p_1(0) dot p_2(3) + p_1(2) dot p_2(1) = 1/3 $
  $ PP(S=4) = p_1(2) dot p_2(2) = 1/6 quad PP(S=5) = p_1(2) dot p_2(3) = 1/6 $
  И функцию распределения:
  $ #hl-math-answer[$F(x) = cases( 
    0 quad & "," x < 1,
    1/6 quad & "," 1 <= x < 2,
    1/3 quad & "," 2 <= x < 3,
    2/3 quad & "," 3 <= x < 4,
    5/6 quad & "," 4 <= x < 5,
    1 quad & "," x >= 5
  )$] $
  $ EE X = sum_(i=1)^5 PP(S=i) dot i = 1/6 + 1/3 + 1 + 2/3 + 5/6 = #hl-math-answer[$3$] $
  $ EE X^2 = 1/6 + 2/3 + 3 + 8/3 + 25/6 = 32/3 $
  $ DD X = EE X^2 - EE^2 X = #hl-math-answer[$5/3$] $
]

#line(length: 100%)
#task()[]
#solution()[
  $ integral_0^x e^(-t) d t = -e^(-x) + 1 $
  $ F_X (x) = cases(
      0 quad & "," x < 0,
      -e^(-x) + 1 quad & "," x >= 0
    )
  $
  $ Y = 1 - e^(-X) ==> X = -ln(1 - Y) $
  Т.к. $X >= 0$, то это значит что случайная величина $Y$ должна принимать значения на промежутке $[0; 1)$. Выразим $F_Y(x)$ через $F_X(x)$:
  $ F_Y (y) = PP(Y < y) = PP(1 - e^(-X) < y) = PP(X < - ln (1 - y)) = F_X (-ln (1 - y)) $
  Значит:
  $ F_Y (y) = cases(
    0 quad & "," y < 0,
    -e^(- (-ln (1 - y))) + 1 quad & "," 0 <= y < 1,
    1 quad & "," y >= 1
  ) = #hl-math-answer[$cases(
    0 quad & "," y < 0,
    y quad & "," 0 <= y < 1,
    1 quad & "," y >= 1
  )$] $
]

#line(length: 100%)
#task()[]
#solution()[
  $ F_Y (y) = PP(Y < y) = PP(F(X) < y) = PP(X < F^(-1)(y)) = F(F^(-1)(y)) = y $
  Заметим что т.к. $F : RR -> [0;1]$, то $F^(-1) : [0; 1] -> RR$. Значит $F_Y (y) = y$ только при $0 <= y <= 1$:
  $ #hl-math-answer[$F_Y (y) = cases(
    0 quad & "," y < 0,
    y quad & "," 0 <= y <= 1,
    1 quad & "," y > 1,
  )$] $
]
