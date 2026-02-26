#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 2],
  date: [26 февраля],
  number: 2,
  program: "ITMO MSE y2025",
  doc
)

= Выборочные характеристики как оценки генеральных

#definition[
  $overline(a)_n$ --- (выборочная характеристика) *состоятельная оценка генеральной*  характеристики $a$, если $overline(a)_n ->^PP a$.
]

#theorem("Гливенко-Кантелли")[
  $ sup_X |overline(F_n) (x) - F(x)| ->_(n -> +infinity) 0 #text[п.н.] $
]

#definition[
  Выборочная характеристика $overline(a)_n$ --- несмещенная ассимптотическая оцнека, если $forall n med EE overline(a)_n = a_i$
]
