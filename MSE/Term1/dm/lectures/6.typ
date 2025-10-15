#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 6],
  date: [15 октября],
  number: 6,
  doc
)

= Дискретная теория вероятностей

#definition()[
  $Omega = {omega_1, omega_2, dots, omega_n}$ --- *множество (пространство) элементарных исходов*.
  - Дизъюнктно --- если произошло одно не может произойти другое. $forall i,j, i != j:$ $omega_i$ и $omega_j$ --- *несовместны*
  - Нужно чтобы хотя бы 1 $omega_i$ произошло
  - Все $omega_i$ равновероятны
]

#definition()[
  $A$ --- *событие*, если $A subset Omega$
  $ PP(A) = (|A|) / (|Q|) $
]

#remark([Свойства])[
  1. $PP(emptyset) = 0$, $PP(Omega) = 1$, $forall A subset Omega, 0 <= PP(A) <= 1$
  2. $PP(A union B) = PP(A) + PP(B) - PP(A inter B)$
  3. $A inter B = emptyset ==> PP(A union B) = PP(A) + PP(B)$
  4. $PP(A) = 1 - PP(overline(A))$
  5. $PP(A union B) <= PP(A) + PP(B)$
  6. ~
    $ PP(union.big_(i = 1)^m A_i) = sum_(i = 1)^m A_i - sum_(1 <= i < j <= m) PP(A_i inter A_j) + sum_(1 <= i < j < k <= m) PP(A_i inter A_j inter A_k) - dots + (-1)^(m - 1) PP(A_1 inter A_2 inter dots inter A_m) $
]

// TODO: Move to common
#let xunderline(stroke: black, equation) = block(
  stroke: (bottom: .5pt + stroke), 
  outset: (bottom: 1.5pt), 
  $ equation $
)

// FIXME: Use #ref
#proof([Свойство 6])[
  По индукции:

  База: $m = 2$ --- это Свойство 2
  
  Переход: $m - 1 mapsto m$
  $
    PP(union.big_(i = 1)^n A_i) = PP(union.big_(i = 1)^(m - 1) A_i union A_m) = PP(union.big_(i = 1)^(m - 1) A_i) + PP(A_m) - PP(union.big_(i = 1)^(m - 1) (A_i inter A_m)) = \

    xunderline(stroke: #red, sum_(i = 1)^(m - 1) PP(A_i)) -
    xunderline(stroke: #blue, sum_(1 <= i < j <= m - 1) PP(A_i inter A_j)) + dots + 
    xunderline(stroke: #red, PP(A_m)) - 
    overbrace(
      xunderline(stroke: #blue, sum_(i = 1)^(m - 1) PP(A_i inter A_m)) - 
      sum_(1 <= i < j <= m - 1) PP(A_i inter A_j inter A_m) + dots,
      #text[По ИП]) = \
    = sum_(i = 1)^m PP(A_i) - sum_(1 <= i < j <= m) PP(A_i inter A_j) + dots
  $
]

== Условные вероятности
#definition()[
  $ P(A | B) = frac(|A inter B|, |B|) = frac(PP(A inter B), PP(B)) quad PP(B) != 0 $
]
#remark([Свойства])[
  1. $PP(emptyset | B) = 0$, $PP(B | B) = 1$, более того если $B subset A$, то $PP(A | B) = 1$
  2. $A_1 inter A_2 = emptyset ==> PP(A_1 union A_2 | B) = PP(A_1 | B) + PP(A_2 | B)$
  3. $PP(A | B) = 1 - PP(overline(A) | B)$
]
#example()[
  $B$ --- выпало четное, $A$ --- выпало кратное $3$.
  $ P(A | B) = frac(1/ 6, 1/2) = 1/ 3 $
]
#theorem([Формула полной вероятности])[
  $Omega = union.sq.big_(i = 1)^m B_i$, тогда
  $ PP(A) = sum_(i = 1)^m PP(A | B_i) dot PP(B_i) $
]
#proof()[
  $ 
    sum_(i = 1)^m PP(A | B_i) dot PP(B_i) = sum_(i = 1)^m frac(PP(A inter B_i), PP(B_i)) dot PP(B_i) = PP(union.big_(i = 1)^m (A inter B_i)) = \
    = PP(A inter (union.big_(i = 1)^m B_i)) = PP(A inter Omega) = PP(A)
  $
]
#example()[
  $1$-ая корзина: 3 белых и 5 черных, $2$-ая корзина: 3 белых и 3 черных. 
  1. Перекладываем 2 шара из 1ой во 2-ую
  2. Выбираем шар из 2-ой корзины

  $A$ --- это белый шар. $PP(A) = ?$. $B_i$ --- переложили $i$ белых шаров
  $ PP(A | B_0) = 3 / 8 quad PP(A | B_1) = 4 / 8 quad PP(A | B_2) = 5 / 8 $
  $ PP(B_0) = frac(binom(5, 2), binom(8, 2)) = 5/8 dot 4/7 = 5/14 quad PP(B_1)  = 3 / 8 dot 2 / 7 = 3/28 quad PP(B_1) = 15 / 28 $
  $ PP(A) = PP(A | B_0) dot PP(B_0) + PP(A | B_1) dot PP(B_1) + PP(A | B_2) dot PP(B_2) = dots = 15/32 $
]

#theorem([Формула Байеса])[
  $PP(A) != 0, PP(B) != 0$, тогда
  $ PP(B | A) = frac(PP(A | B) dot PP(B), PP(A)) $
]
#proof()[
  $ frac(PP(A | B) dot PP(B), PP(A)) = frac(PP(A inter B) / PP(B) dot PP(B), PP(A)) = PP(A inter B) / PP(A) = PP(B | A) $
]
#theorem([Байеса])[
  $Omega = union.sq.big_(i = 1)^m B_i$, $PP(A) != 0$
  $ PP(B_k | A) = frac(PP(A | B_k) dot PP(B_k), sum_(i = 1)^m PP(A | B_i) dot PP(B_i)) $
]
#example()[
  Два кубика:
  1. обычный
  2. с гранями 1, 1, 2, 2, 3, 3
  Какая вероятность что мы бросили обычный кубик если выпала 2.

  $A$ --- выпала 2, $B_i$ --- кидали $i$-ый кубик
  $ PP(B_1 | A) = frac(PP(A | B_1) dot PP(B_1), PP(A | B_1) dot PP(B_1) + PP(A | B_2) dot PP(B_2)) $
  $ PP(B_1) = PP(B_2) = 1 / 2 quad PP(A | B_1) = 1 / 6 quad PP(A | B_2) = 1 / 3 $
  $ PP(B_1 | A) = 1 / 3 $
]

== Независимость
$ PP(A inter B) / PP(B) = PP(A | B) = PP(A) $
#definition()[
  Если $PP(A inter B) = PP(A) dot PP(B)$, то события $A$ и $B$ *независимы*
]
#definition()[
  $A_1, A_2, dots, A_m$ --- события. Называются независимыми в совокупности, если для любого поднабора индексов $j$:
  $ PP(A_(j_1) union A_(j_2) union dots union A_(j_k)) = PP(A_(j_1)) dot PP(A_(j_2)) dot dots dot PP(A_(j_k)) $
]
#remark()[
  Здесь $2^m - m - 1$ содержательных условий
]

#example([Пирамида кого-то])[
  Дан тетраедр с покрашеными сторонами:
  1. красный
  2. белый
  3. синий
  4. и красный и белый и синий
  $A$ --- на выпавшей грани есть белый цвет, $B$ --- синий, $C$ --- красный.
  $
    PP(A) = PP(B) = PP(C) = 1/ 2 \
    PP(A inter B) = PP(B inter C) = PP(C inter A) = 1 /4  \
    PP(A inter B inter C) = 1 / 4
  $
  Пример задачи где $P(A inter B) = P(A inter B inter C)$
]
