#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 1],
  date: [11 февраля],
  number: 1,
  author: "Ярошевский Илья",
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  $ (N_1 ~> N'_1) / ("if" M "then" N_1 "else" N_2 ~> "if" M "then" N_1' "else" N_2) $
  $ (N_2 ~> N'_2) / ("if" M "then" V_1 "else" N_2 ~> "if" M "then" V_1 "else" N'_2) $
  $ (M ~> M') / ("if" M "then" V_1 "else" V_2 ~> "if" M' "then" V_1 "else" V_2) $
  $ "if" "true" "then" V_1 "else" V_2 ~> V_1 $
  $ "if" "false" "then" V_1 "else" V_2 ~> V_2 $
]

