#import "../../../other/typst/practice_mse.typ": *

#show: doc => practice(
  subj: [Функциональное програмирование],
  title: [Практика 2],
  date: [17 сентября],
  number: 2,
  doc
)

// FIXME(iliayar): better spaces for lambda terms
#let term(name) = text(name, weight: "bold")
#let lam = [$lambda$ #h(0pt)]

#remark()[
  Кодирование по Черчу --- элиминатор ничего не делает
]

= Примитивная рекурсия

$
  term("init") colon.eq lam "init". term("pair") term("0") term("init") \
  term("iter") colon.eq lam f. lam p. term("pair") thin (term("succ") thin (term("fst") thin p)) (f thin (term("fst") thin p) (term("snd") thin p)) \
  term("rec") colon.eq lam f. lam "init". lam n. term("snd") thin (n thin (term("iter") thin f) thin (term("init") thin "init")) \
  term("sumN") colon.eq term("rec") thin term("add") thin term("0") thin (term("succ") thin n) \
  term("fact") colon.eq term("rec") thin term("mult") thin term("1") thin (term("succ") thin n) \
  term("pred") colon.eq term("rec") thin (lam a. lam b. a) thin term("0") thin n
$

= Рекурсивне уравнения
$
  term("fac") N eq_beta term("if") (term("isZero") N) thin term("1") thin (term("mult") N thin (term("fact") (term("pred") N))) \
  term("fac") N eq_beta underbrace(lam r. lam n. term("if") (term("isZero") n) thin term("1") thin (term("mult") N thin (r thin (term("pred") thin n))), term("fac'")) term("fac") N \
  term("fac") eq_beta term("fac'") term("fac") \
  term("fac") eq_beta term("Y") term("fac'")
$
