#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 5],
  date: [8 октября],
  number: 5,
  doc
)

= Рекуррентные соотношения

#definition()[
  $a_(n + m) = f_n (a_(n + m - 1), a_(n + m - 2), dots, a_n)$ --- *рекуррентное соотношение* (рекуррента) $m$-того порядка, где $a_0, a_1, dots, a_(m - 1)$ --- начальные условия

  Будем рассматривать рекуррентные соотношения вида $a_(n + m) = b_1(n) dot a_(n + m - 1) - b_2(n) dot a_(n + m - 2) + dots + b_,(n) dot a_n + u(n)$ --- линейное рекуррентное соотношение. $a_(n + m) = b_1 dot a_(n + m - 1) + b_2 dot a_(n + m - 2) + dots + b_m a_n + u(n)$ --- линейное рекуррентное соотношение с постоянными коэффициентами.
  
  Если $u(n) equiv 0$, тогда линейное рекуррентное соотношение называется однородным.
]

$a_(n + 2) = b dot a_(n + 1) + c dot a_n$. Попробуем найти ответ в виде $a_n = lambda^n$.
$
  lambda^(n + 2) = b dot lambda^(n + 1) + c dot lambda^n \
  lambda^2 - b lambda - c = 0 #text[ --- характеристическое уравнение]
$

#remark()[
  $lambda_1 != lambda_2$ --- вещественные корни характеристического уравнения
  $
    a_n = c_1 lambda_1^n + c_2 lambda_2^n #text[ --- общее решение] \
    c_1 lambda_1^(n + 2) + c_2 lambda_2^(n + 2) = b(c_1 lambda_1^(n + 1) + c_2 lambda_2^(n + 1)) + c(c_1 lambda_1^n + c_2 lambda_2^n) \
    c_1 lambda_1^n (lambda_1^2 - b lambda_1 - c) + c_2 lambda_2^n (lambda_2^2 - b lambda_2 - c) = 0
  $
] <first-case-roots>

#example()[
  Количество способов разбить полоску длины $n$, ширины $2$ доминошками $2 times 1$.
  $ a_(n + 2) = a_(n + 1) + a_n $
  Характеристическое уравнение $lambda^2 - lambda - 1 = 0$, где $lambda = frac(1 plus.minus sqrt(5), 2)$
  $ 
    a_n^(#text[общ.]) = c_1 (frac(1 + sqrt(5), 2))^n + c_2 (frac(1 - sqrt(5), 2))^n \
    cases(
      0 = c_1 + c_2,
      1 = c_1 dot frac(1 + sqrt(5), 2) + c_2 frac(1 - sqrt(5), 2)
    ) \
    c_1 = (sqrt(5))^(- 1) quad c_2 = (-sqrt(5))^(-1) \
    F_n = frac((frac(1 + sqrt(5), 2))^n - (frac(1 - sqrt(5), 2))^n, sqrt(5)) #text[ --- Формула Бине]
  $
]
#remark()[
  $ frac(1 + sqrt(5), 2) = Phi quad frac(1 - sqrt(5), 2) = Psi$
]

#remark()[
  $lambda_1$ --- корень характеристического уравнения кратности $2$
  $ 
    a_n^(#text[общ.]) = c_1 lambda_1^n + c_2 n lambda_1^n \
    (n + 2) lambda_1^(n + 1) = b(n + 1) lambda_1^n + c dot n lambda_1^(n - 1) \
    underbrace((n + 2) lambda^(n + 2), (a_(n + 2))) = b underbrace((n + 1) lambda_1^(n  +1 ), a_(n + 1)) + c underbrace(n lambda_1^n, a_n)
  $
]

#lemma()[
  Формула Муавра
  $ (cos phi plus.minus i sin phi)^n = cos n phi plus.minus i sin n phi $
]

#remark()[
  Характеристическое уравнение имеет $2$ комплексных корня
  $ lambda_(1, 2) = alpha plus.minus beta i = r (cos phi plus.minus i sin phi) $
  - Если попали в #link(<first-case-roots>)[первый случай]
    $ 
      a_n^(#text[общ.]) = c_1 (alpha + beta i)^n + c_2 (alpha - beta i)^n = \
      = r^n ( c_1 (cos phi + i sin phi)^n  + c_2 (cos phi - i sin phi)^n) = \
      = r^n ((c_1 + c_2) cos (n phi) + i (c_1 - c_2) sin (n phi) ) = \
      = r^n (tilde(c_1) cos n phi + tilde(c_2) sin n phi)
    $
  - Если попали в #link(<first-case-roots>)[второй случай]
    $ a_(n + m) = b_1 dot a_(n + m - 1) + dots + b_m a_n + P(n) dot p^n $
    Алгоритм:
    1. Решаем ответствующее однородное уравнение
    2. Находим частное решение(я). Оно ищется в виде
      $ a_n^(#text[част.]) = Q(n) dot n^l dot p^n $
      , где $Q(n)$ --- произвольный многочлен такой же степени что и $P(n)$, $l$ --- кратность $p$ как корня характеристического уравнения из шага 1
    3. $a_n^(#text[общ.]) = a_n^(#text[одн.]) + a_n^(#text[част.]) + dots$
    4. подбор коэффициентов под начальные условия
]

#remark()[
  $u(n) = P(n) dot sin (n phi) dot p^n$
  $ a_n^(#text[част.]) = Q(n) dot n^l (sin n phi + cos n phi) dot p^n$
]
