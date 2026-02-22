#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Лекции по Теории Типов],
  title: [Лекция 2],
  date: [18 февраля],
  number: 2,
  program: "ITMO MSE y2025",
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  $ prooftree(rule(dots, tack (lambda x^#[`Bool`]. med x) med #[`true`] : #[`Bool`])) $
]
