#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 1],
  date: [12 февраля],
  number: 1,
  program: "ITMO MSE y2025",
  doc
)

= Введение

#definition[
  $cal(P)$ --- распределение на прямой. $X_1, dots, X_n$ --- н.о.р.с.в.
]

#definition[
  *Выборочное (эмпирическое) распределение* --- дискретное равномерное распределение с атомами в точках выборки
  $ overline(cal(P)_n) = mat(X_1, dots, X_n; 1/n, dots, 1/n) $
]

#remark[
  Считаем что наши $X_i$ это числа. Вообще так делать нельзя. Хотим вообще говоря считать распределние на случайных величинах. Попробуем найти связь между эти $cal(P)$ и $overline(cal(P)_n)$.
]

#definition[
  *Выборочная характеристика*. $Pi$ --- множество всех распределение на прямой. $T : Pi -> overline(RR) = RR union {+infinity}$ --- характреистика. $T(cal(P))$ --- генеральная характеристика, $T(overline(cal(P)_n)$ --- эмпирическая характеристика
]

#example[
  1. Математическое ожидание.
     $ m_1 = T(cal(P)) = integral_RR z cal(P) (d z) $
     $ overline(X) = overline(m_1) = T(overline(cal(P)_n)) = dots = 1/n sum_(i = 0)^n X_i $
  2. Дисперсия
     $ dots = 1/n sum_(i = 0)^n (X_i - overline(X))^2 $
  3. Стандартное отклонение, Выборочное стандартное отклонение
  4. Момент порядка $k$
     $ m_k = integral_RR z^k cal(P)(d z) $
     $ overline(m_k) = 1 / n sum_(i = 0)^n X_i^k $
  5. Центральные моменты
     $ m_k^((0)) = integral_RR (z - m_1)^k cal(P)(d z) $
     $ overline(m_k^((0))) = 1/n sum_(i = 1)^n (X_i - overline(X))^k $
  6. Ковариация $(X_i, Y_i)$
     $ "cov"(X, Y) = integral_RR (u - m_X) (v - m_Y) cal(P)(u, v) #fixme() $
  7. Коэффициент кореляции
  8. Функция распределения
     $ F(z) = T(cal(P)) = P(X_i <  z) $
] 

#definition[
  *Эмпирическая функция распределения*
  $ overline(F_n)(z) = overline(cal(P)_n)((-infinity, z)) = undershell(\#{X_i < z}, n) $
  $ F_n (x) = 1/n sum_(i = 1)^n bb(1)(x_i <= x) $
]

#remark[
  Индекс в вариационномр ряде $X_[i]$.
]

#definition[
  Квантили $0 < p < 1$ это решение уравнения $F(z_p) = p$
]

#definition[
  $z_p$ --- $p$-квантиль для $cal(P)$, если $z_p = sup { z : F(z) < p }$. Эмпирические квантили $overline(z_p) = sup {z : overline(F_n)(z) <= p}$
]

#example[
  $z_(1/2)$ --- медиана
]

#task[
  $overline(z_p) : X_([floor(n p) + 1])$
]
