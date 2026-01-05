#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных],
  title: [Лекция 2],
  date: [17 сентября],
  number: 2,
  program: "ITMO MSE y2024",
  doc
)

= #todo() Простые структуры данных
Массив, стек, очередь, дек, вектор, связный список

= Амортизационный Анализ

#definition()[
  $ frac(sum_(i = 1)^n #text[time]_i, n) = #text[average] $
]

#definition()[
  Потенциал: $forall phi_i in RR$.
  $ a_i = #text[time]_i + Delta phi quad Delta phi = phi_(i + 1) - phi_i $
  где $a_i$ -- *амортизированное время*
]
#remark()[
  $ sum_(i = 1)^m a_i = sum_(i = 1)^m #text[time]_i + (phi_m - phi_0) $
  $ frac(sum_(i = 1)^m a_i, m) = frac(sum_(i = 1)^m #text[time]_i, m) + frac(phi_m - phi_0, m) $
]
#theorem()[
  $ forall phi quad frac(sum_(i = 1)^m #text[time]_i, m) <= max a_i + frac(phi_0 - phi_m, m) $
]
#proof()[
  Очевидно, учитывая что $frac(Sigma, m) <= max$
]

#remark()[
  $phi_0 = 0 med forall i : phi_i >= 0 ==> frac(phi_0 - phi_m, m) <= 0 ==>$
  $ frac(sum #text[time]_i, m) <= max a_i $
]

#example()[
  Рассмотрим вектор. $phi = - #text[capacity]$. Рассмотрим два случая $a_i = #text[tim]_i + Delta phi$:
  - Не реаллоицировали: $a_i = 1 + 0 = 1$
  - Реаллоцировали: $a_i = n + (-n) = 0$
  $ a_i = Theta(1) ==> frac(sum #text[time]_i, m) = Theta(1) + frac(2m, m) = cal(O)(1) $
]

== Очередь с минимумами
Реализуется на 2 стеках с минимумами ($A, B$).

#pseudocode-list("Доступные операции")[
  - #smallcaps[Push] ($x$)  
    + $A."Push"(x)$  
  -
  - #smallcaps[Pop] ($x$)  
    + *if* $B."Empty"()$
      + *while* $not A."Empty"()$ --- $cal(O)(|A|)$
        + $B."Push"(A."Pop"())$
    + *return* $B."Pop"()$
  -
  - #smallcaps[Min] ()
    + *return* $min(A."Min"(), B."Min"())$
]

#example()[
  $phi = |A|$
  - Min :: $a_i = 1 + 0$
  - Push :: $a_i = 1 + 1$
  - Pop :: $a_i = cases(1 + 0, |A| - |A| = 0)$
  $ frac(sum #text[time]_i, m) <= max a_i = Theta(1) $
]
