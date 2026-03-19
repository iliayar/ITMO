#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 5],
  date: [19 марта],
  number: 5,
  program: "ITMO MSE y2025",
  doc
)

#definition[
  Случайная величина $g(X_1, dots, X_n; theta)$ --- центральная статистика для $theta$:
  1. $g(X_1, dots, X_n; theta$ --- не зависит от $theta$.
  2. $G_n$ --- функция распределения центрального распределения непрерывна
  3. $forall z_1, z_2 : z_1 < g(X_1, dots, X_n; theta) < z_2 med exists f_1, f_2 med forall theta med f_1(X_1, dots, X_n; z_1, z_2) < theta < f_2(X_1, dots, X_n; z_1, z_2)$.
]

#theorem[
  $X_1, dots, X_n$ --- н. о. р $DD X_i = sigma^2 < +infinity$, $EE X_i = 1$
  $ sqrt(n) (overline(X) - a) / sigma ->_(n -> infinity)^d cal(N)(0, 1) $
  $ PP(z_1 < (overline(X) - a) / sigma < z_2) ->_(n -> infinity) Phi(z_2) - Phi(z_1) $
]
