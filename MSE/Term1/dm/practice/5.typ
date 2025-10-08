#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 5],
  date: [8 октября],
  number: 5,
  doc
)

#task(numbering: (_, n) => n)[
  $ a_(n + 2) = 5 a_(n + 1) - 6 a_n, a_0 = 2, a_1 = 6 $
]
#solution()[
  Порядок 2, поэтому зар. многочлен второй степени 
  $
    lambda^2 - 5 lambda + 6 = 0 quad lambda_1 = 2, lambda_2 = 3 \
    a_n = c_1 dot 2^n + c_2 dot 3^n \
    cases(
      a_0 : 2 = c_1 + c_2,
      a_1 : 6 = c_1 dot 2 + c_2 dot 3
    ) quad c_1 = 0, c_2 = 2 \
    q_n = 0 dot 2^n + 2 dot 3^n = 2 dot 3^n
  $
]

#task(numbering: (..) => numbering("1.a", 2, 1))[ #todo() ]
#solution()[
  $
    a_(n + 2) = - 4 a_(n + 1) - 4 a_n \
    lambda^2 + 4 lambda +4 = 0 quad lambda_(1, 2) = -2 \
    a_n = (c_1 + c_2 n) (-2)^n
  $
]

#task(numbering: (..) => numbering("1.a", 2, 2))[ #todo() ]
#solution()[
  $
    a_(n + 2) = 2 sqrt(3) a_(n + 1) - 4 a_n \
    lambda^2 - 2 sqrt(3) lambda + 4 = 0 quad lambda_(1, 2) = sqrt(3) plus.minus i
  $
  Переведем в полярные координаты, модуль $sqrt(3 + 1) = 2$
  $
    cos alpha = frac(sqrt(3), 2) quad sin alpha = frac(1, 2) quad alpha = pi / 6 \
    a_n = 2^n (c_1 sin frac(pi n, 6) + c_2 cos frac(pi n, 6))
  $
]

#task(numbering: (..) => numbering("1", 3))[ #todo() ]
#solution()[
    $
      a_(n + 5) = 2 a_(n + 4) + 16 a_(n + 1) - 32 a_n \
      lambda^5 - 2 lambda^4 - 16 lambda + 32 = 0 \
      (lambda - 2) (lambda ^2 - 4) (lambda^2 + 4) = 0 \
      (lambda - 2)^2 (lambda + 2) (lambda^2 + 4) = 0 \
      lambda_1 = 2, lambda_2 = -2. lambda_(3, 4) = plus.minus 2 i [r = 2, phi = pi / 4] \
      a_n = overbrace(c_1 (-2)^n, lambda_2) + overbrace((c_2 + n c_3) 2^n, lambda_1) + overbrace(2^n (c_4 cos frac(pi n, 2) + c_5 sin frac(pi n, 2)), lambda_(3, 4))
    $
]

#task(numbering: (..) => numbering("1", 4))[ #todo() ]
#solution()[
  $
    a_(n + 2) = 5 a_(n + 1) - 4a_n + underbrace(3 dot 2^n, U(n)) \
    lambda^2 - 5 lambda + 4 = 0 quad lambda_1 = 1, lambda_2 = 4 \
    a_n = p_n + q_n \
    p_n = c_1 + c_2 dot 4^n \
    q_n = c 2^n n^0 #text[[$n$ в степени кратности корня $2$]] \
    c dot 2^(n + 2) = 5 dot c 2^(n + 1) - 4 c dot 2^n + 3 2^n \
    c dot 4 = 5 dot c dot 2 - 4 c + 3 \
    c = - 3 / 2 ==> q_n = -3 dot 2^(n - 1) \ 
    a_n = c_1 + c_2 dot 4^n - 3 dot 2^(n - 1)
  $
]

#task(numbering: (..) => numbering("1", 5))[ #todo() ]
#solution()[
  $
    a_(n + 2) = 3 a_(n + 1) - 2 a_n + underbrace(3 sin frac(pi n, 2), U(n)) \
    sin frac(pi n, 2) = frac(e^(frac(i pi n, 2)) - e^(frac(-i pi n, 2)), 2i) = \
    = frac(3, 2i) ((e^(frac(i pi, 2)))^n - (e^(frac(-i pi, 2)))^n) = frac(3, 2i) (r_1^n - r_2^n)
  $
  Пусть $q_n = c cos frac(pi n, 2) + d sin frac(pi n, 2)$
  $
    c dot cos frac(pi (n + 2), 2) + d dot sin frac(pi (n + 2), 2) = 3 c cos frac(pi n + pi, 2) + 3 d sin frac(pi n + pi, 2) - 2 c cos frac(pi n, 2) - 2 d sin frac(pi n, 2) + 3 sin frac(pi n , 2) \
    cos frac(pi n, 2) (-c - 3d + 2c) + (-d + 3c + 2d - 3) sin frac(pi n, 2) = 0 \
    cases(
      c - 3 = 0,
      3c + d = 3
    ) quad c = 0.9, d = 0.3 \
    a_n = c_1 + c_2 dot 2^n + 0.9 cos frac(pi n, 2) + 0.3 sin frac(pi n, 2)
  $
]

#task(numbering: (..) => numbering("1", 5))[ #todo() ]
#solution()[
  Возьмем одного нового, способов поставит ему в пару $2n - 1$.
  $ 
    a_(2n) = (2n - 1) a_(2n - 2) = (2n - 1)!!
  $
]
