#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 10],
  date: [19 ноября],
  number: 10,
  doc
)

= Численные характеристики случайный величин (продолжение)

#definition()[
  - $EE xi^k$ --- $k$-тый момент
  - $EE |xi|^k$ --- $k$-тый абсолютный момент
  - $EE (xi - EE xi)^k$ --- $k$-тый центральный момент
  - $EE |xi - EE xi|^k$ --- $k$-тый центральный абсолютный момент
]

#definition()[
  Ковариация $xi$ и $eta$ : $EE ((xi - EE xi) (eta - EE eta)) eq.colon "cov"(xi, eta)$
]

// TODO: Move to common
#let xunderline(stroke: black, equation) = block(
  stroke: (bottom: .5pt + stroke), 
  outset: (bottom: 1.5pt), 
  $ equation $
)

#properties()[
  1. $"cov"(xi, xi) = DD xi$
  2. $"cov"(xi, eta) = "cov"(eta, xi)$
  3. $"cov"(xi, eta)$ --- линейна по каждой переменной
  4. $"cov"(xi, eta) = EE xi eta - EE xi dot EE eta$
    #proof()[
      $ EE((xi - EE xi) (eta - EE eta)) = EE (xi eta - eta dot EE xi - xi dot EE eta + EE xi dot EE eta) = \
        = EE xi eta - EE xi dot EE eta - EE eta dot EE xi + EE xi dot EE eta = EE xi eta - EE xi dot EE eta
      $
    ]
  5. Если $xi$ и $eta$ независимы то $"cov"(xi, eta) = 0$
    #remark()[
      Почему в обратную сторону не верно. $xi = cases(-1 "," 1/3, 0 "," 1/3, 1 "," 1/3)$. $eta = xi^2$.
      Очевидно что они зависимы. Покажем что ковариация не $0$:
      $ EE xi = 0 quad EE xi eta = EE xi^3 = EE xi = 0 quad EE xi eta = 0 = EE xi dot EE eta ==> "cov"(xi, eta) = 0 $
    ]
  6. $DD (xi + eta) = DD xi + DD eta + 2 "cov"(xi, eta)$
  7. $DD (sum_(i = 1)^n xi_i = sum_(i = 1)^n DD xi_1 + 2 sum_(i < j) "cov"(xi_i, xi_j)$
    #proof()[
      $ DD (sum_(i = 1)^n xi_i) = EE (sum_(i = 1)^n xi_i - EE sum_(i = 1)^n xi)^2 = EE((sum_(i = 1)^n xi_i^2) + (EE sum_(i = 1)^n xi)^2 - 2 dot sum xi_i dot EE sum xi_i) = \
        = EE sum xi_i^2 + 2 EE sum_(i < j) xi_i xi_j + (EE sum xi_i)^2 - 2 (EE sum xi_i)^2 = EE sum xi_i^2 + 2 EE sum_(i < j) xi_i xi_j - (sum EE xi_i)^2 = \
        = xunderline(stroke: #blue, EE sum xi_i^2) + xunderline(stroke: #green, 2 EE sum_(i < j) xi_i xi_j) - xunderline(stroke: #blue, sum EE^2 xi_i) - xunderline(stroke: #green, 2 sum_(i < j) EE xi_i EE xi_j) = xunderline(stroke: #blue, sum_(i = 1)^n DD xi_i) + xunderline(stroke: #green, 2 sum_(i < j) "cov"(xi_i, xi_j))
      $
    ]
]

#theorem([Неравенство Коши-Буняковского-Шварца])[
  $ |"cov"(xi, eta)| <= sqrt(DD xi dot DD eta) $
]
#proof()[
  $2 |x y| <= (alpha^2 x^2 + 1/alpha^2 y^2)$
  $ 0 <= (alpha^2 |x|^2 - 2 dot |x| dot |y| + 1/alpha^2 |y|^2) = (alpha |x| - 1/alpha |y|)^2 $
  $ 2 | EE xi eta| <= 2 EE |xi eta| <= EE (alpha^2 xi^2 + 1/alpha^2 eta^2) $
  $ xi arrow.squiggly xi' - EE xi' quad eta arrow.squiggly eta' - EE eta' $
  $ 2 |"cov"(xi', eta')| <= alpha^2 dot DD xi' + 1/alpha^2 DD eta' = 2 sqrt(DD eta' dot DD xi') $
  $ alpha^2 = sqrt(DD eta' / DD xi') ==> |"cov"(xi, eta)| <= sqrt(DD xi dot DD eta) $
]

#definition()[
  $r(xi, eta)$ --- коэффициент корреляции $xi$ и $eta$
  $ r(xi, eta) colon.eq ("cov"(xi, eta))/sqrt(DD xi dot DD eta) $
]
#properties()[
  1. $r(xi, eta) in [-1, 1]$ (по свойству 8 (неравенство КБШ)
  2. $r(xi, eta) = r(eta, xi)$
  3. $r(a xi + b, c eta + d) = "sign"(a dot c) dot r(xi, eta)$
    #proof()[
      $ r(a xi + b, c eta + d) = ("cov"(a xi + b, c eta + d)) / sqrt(DD (a xi + b) dot DD (c eta + d)) = (a c dot "cov"(xi, eta)) / sqrt(a^2 dot DD xi dot c^2 dot DD eta)  = (a c dot "cov"(xi, eta)) / (|a c| sqrt(DD xi dot DD eta))$
    ]
  4. $r(xi, xi) = 1$
  5. $xi$, $eta$ --- независимые $==> r(xi, eta) = 0$
  6. $r(xi, eta) = plus.minus 1 <==> xi = a eta + b$ (причем знак $r$ совпадает со знаком $a$)
    #proof()[
      - $(<==)$ доказано по предыдущим свойствам
      - $(==>)$ $angle.spheric xi' = xi / sqrt(DD xi), eta' = eta/sqrt(DD eta)$
        $ plus.minus 1 = r(xi, eta) = "cov"(xi, eta) / sqrt(DD xi dot DD eta) $
        $ angle.spheric DD (xi' - eta') = DD xi' + DD eta' - 2 "cov"(xi', eta') = 2 - 2 dot ("cov"(xi, eta)) / sqrt(DD xi dot DD eta) = 0 $
        $ D xi' = DD ((xi - EE xi) / sqrt(DD xi)) = 1 / (DD xi) dot DD (xi - EE xi) = 1 $
      #todo()
    ]
]

= Сходимости случайных величин

$xi_1, xi_2, dots$ --- случайные величины : $Omega -> RR$

#definition()[
  $xi_n -> xi$ почти наверное
  $ PP(omega in Omega : xi_n(omega) -->_(n -> infinity) xi(omega)) = 1 $
]

#definition()[
  $xi_n -->_(n -> infinity)^(L_p) xi$ сходится в среднем порядка $p$
  $ EE |xi_n - x|^p --> 0 $
]

#definition()[
  $xi_n -->^PP xi$ по вероятности
  $ forall epsilon > 0 quad PP(|xi_n - xi| > epsilon) -->_(n -> infinity) 0 $
]

#definition()[
  $xi_n -->^d xi$ сходимость по распределению
  $ forall x in C_(F_xi) quad F_(xi_n)(x) --> F_xi (x) $
  $C_(F_xi)$ --- точки непрерывности $F_xi$.
]

== Связь сходимостей

// TODO(iliayar): Diagram of implications
#remark()[
- 1. $==>$ 3. по т. Лебега
- 2. $==>$ 3.
  #proof()[
    $forall epsilon  quad PP(|xi_n - xi| > epsilon) <= (EE |xi_n - xi|^p) / epsilon^p --> 0$ по неравенству Маркова
  ]
- 1. $arrow.double.not$ 2. (тогда и 3. $arrow.double.not$ 2.)
  #proof()[
    $Omega : [0; 1] quad xi_n = n^p dot bb(1)_([0; 1/n]) quad xi_n --> 0$ почти наверное
    $ EE |xi_n - 0|^p = EE n dot bb(1)_([0; 1/n]) = n dot EE bb(1)_([0; 1/n]) = n dot 1 / n = 1 arrow.not 0 $
  ]
- 2. $arrow.double.not$ 1. (тогда и 3. $arrow.double.not$ 1.)
  #proof()[
    Рассмотрим последовательность $eta_(1, 0), eta_(2, 0), eta_(2, 1), eta_(3,0), eta_(3,1), eta_(3, 2), dots$
    $ eta_(n,k) = bb(1)_([k / n; (k + 1) / n]) quad EE |eta_(n, k) - 0|^p = 1/n --> 0 $
    $eta_(n, k) arrow.not 0$ почти наверное
  ]
- 4. $arrow.double.not$ 3. (тогда и 4. $arrow.double.not$ 1. и 4. $arrow.double.not$ 2.)
  #proof()[
    $xi_1, xi_2, dots$ --- н.о.р.с.в (независимые и одинаково распределенные случайные величины). $F_(xi_n) (x) --> F_xi (x)$ (это буквально один ф.р)
    $ epsilon = 1/2 quad PP(|xi_n - xi| > 1/2) = 1/2 arrow.not 0 $
  ]
- 3. $==>$ 4.
  #proof()[
      $forall epsilon PP(|xi_n - xi| > epsilon) --> 0$. Хотим проверить что $F_(xi_n) (x) --> F_xi(x)$, т.е. $PP(xi_n <= x) --> PP(xi <= x)$.
      1. ${xi_n <= x} supset {xi + epsilon <= x} \\ {|xi_n - xi| > epsilon}$
        $ PP(xi_n <= x) >= PP({xi + epsilon <= x} \\ {|xi_n - xi| > epsilon}) >= PP(xi + epsilon <= x) - PP(|xi_n - xi| > epsilon) $
        $ underline(lim) PP (xi_n <= x) >= F_xi (x - epsilon) $
      2. ${xi_n > x} supset {xi - epsilon > x} \\ {|xi_n - xi| > epsilon}$
        $ PP(xi_n > x) >= PP(xi - epsilon > x) - PP(|xi_n - xi| > epsilon) $
        $ 1 - PP(xi_n <= x) >= 1 - F_xi(x + epsilon) - PP(|xi_n - xi| > epsilon) $
        $ PP(xi_n <= x) <= F_xi(x + epsilon) + PP(|xi_n - xi| > epsilon) $
        $ overline(lim) PP(xi_n <= x) <= F_xi (x + epsilon) $
      $ F_xi (x - epsilon) <= underline(lim) F_(xi_n) (x) <= overline(lim) F_(xi_n) (x) <= F_xi (x + epsilon) $
      $ underline(lim) = overline(lim) = lim = F_xi (x) $
  ]
]
