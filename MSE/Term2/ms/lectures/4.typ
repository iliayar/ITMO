#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 4],
  date: [12 марта],
  number: 4,
  program: "ITMO MSE y2025",
  doc
)

#theorem[
  #todo()
]

#corollary[
  - Оценка максимального правдоподобия $hat(theta)_n$ --- состоятельна
  - ОМП $hat(theta)_n$ --- ассимптотически несмещенная
  - и $DD hat(theta)_n -> 1 / I(theta)$
]

#theorem("Неравеснтво Рао-Крамера")[
  $ DD hat(theta)_n >= (1 + b'_n) $
  #todo()
]
