#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 3],
  date: [5 марта],
  number: 3,
  program: "ITMO MSE y2025",
  doc
)

= Продолжение

$X_1, dots, X_n ~ cal(P)_theta, theta in Theta subset RR^perp$

#definition[
  Оценка --- любая (измерима?) функция выборки, не зависиящая от значения неизвестного параметра. $hat(theta)_n (X_1, dots, X_n)$
]

#definition[
  $hat(theta)_n$ --- несмещенная оценка параметра $theta$, если $forall n med forall theta in Theta med EE hat(theta)_n = theta$
]

#definition[
  $hat(theta)_n$ --- ассимпототически несмещена. если $forall theta in Theta med EE hat(theta)_n ->_(n -> +infinity) theta$
]

#definition[
  $hat(theta)_n$ --- состоятельная (consistent) если $forall theta in Theta med hat(theta)_n ->^PP theta$
]

= Способы построения оценок

1. Способы построения оценок (подстановки моментов). $T : Pi -> overline(RR) ({cal(P)_theta} -> overline(RR))$
