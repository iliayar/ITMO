#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 1],
  date: [19 февраля],
  number: 1,
  doc
)

#task(numbering: (..) => numbering("1", 3))[
  1. 
     $ EE[F_n(x)] = EE[1/n sum_(i = 1)^n bb(1) {x_i <= x}] = 1/n sum_(i = 1)^n EE[bb(1) {x_i <= x}] = \
       = 1/n sum_(i = 1)^n PP(x_i <= x) = 1/n sum_(i = 1)^n F(x) = F(x)
     $

  2. 
    $ DD [F_n(x)] = DD [sum_(i = 1)^n bb(1) {x_i <= x}] = sum_(i = 1)^n DD[bb(1) {x_i <= x}] = n F(x) (1 - F(x)) $
  3. 
    $ DD[F_n(x) - F_n(y)] = DD[1 / n sum_(i = 1)^n (bb(1) {x_i <= x} - bb(1) {x_i <= y})] = DD[1/n sum_(i = 1)^n bb(1) {x_i in (x; y]}] = \
      = 1 / n^2 DD["Bin"(n, F(x) - F(y))] = 1/n^2 dot n dot (F(x) - F(y)) dot (1 - (F(x) - F(y)))
    $
]

