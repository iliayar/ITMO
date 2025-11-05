#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 9],
  date: [5 ноября],
  number: 9,
  doc
)

= Совместное распределение

#definition()[
  Случайные величины $xi_1, xi_2, dots, xi_n$ называются независимыми, если $forall A_1, A_2, dots, A_n$ --- борелевских подмножеств $RR$: события ${xi_1 in A_1}, {xi_2 in A_2}, dots, {xi_n in A_n}$.

  *или* $PP(xi_1 in A_1, xi_2 in A_2, dots, x_n in A_n) = PP(xi_1 in A_1) dot PP(xi_2 in A_2) dot dots dot PP(xi_n in A_n)$
]

#definition()[
  Случайные величины $xi_1, xi_2, dots$ называются независимыми если $forall n quad xi_1, xi_2, dots, xi_n$ --- независимы.
]

#symb()[
  $arrow(xi) = (xi_1, dots, xi_n)$
]

#definition()[
  Совместным распределением $arrow(xi)$ называется мера $Rho_arrow(xi)$ заданная на всех борелевских подмножества $RR^n$: \
  $Rho_arrow(xi) ( B) colon.eq PP(arrow(xi) in B) = PP(omega in Omega : (xi_1(omega), xi_2(omega), dots, xi_n (omega)) in B)$.
]

#statement()[
  $x_1, dots, xi_n$ независимы $<==>$  $Rho_arrow(xi) = Rho_(xi_1) times Rho_(xi_2) times dots times Rho_(xi_n)$
]
#proof()[
  - "$==>$"
    $ Rho_arrow(xi) (B) = PP(arrow(xi) in B) = PP((xi_1, dots, xi_n) in B_1 times B_2 times dots times B_n) = PP(xi_1 in B_1, xi_2 in B_2, dots, xi_n in B_n) = \
      = PP(xi_1 in B_1) dot PP(xi_2 in B_2) dot dots dot PP(xi_n in B_n) = Rho_(xi_1) (B_1) times dots times Rho_(xi_n) (B_n)
    $
  - "$<==$" проверим на ячейках 
    $ PP(arrow(xi) in (a; b]) = PP(xi_1 in (a_1; b_1], dots, xi_n in (a_n; b_n]) = PP(xi_1 in (a_1; b_1]) dot dots dot PP(xi_n in (a_n; b_n]) $
    #todo()
]

#definition()[
  Совместной функцией распределения $F_arrow(xi) (arrow(x))$ называется функция $RR^n -> RR$:
  $ F_arrow(xi) (arrow(x)) = PP(xi_1 <= x_1, xi_2 <= x_2, dots, xi_n <= x_n) $
]

#definition()[
  Совместной плотностью $P_arrow(xi) (arrow(x))$ называется измеримая функция $RR^n -> RR_+$ :
  $ F_arrow(xi) (arrow(x)) = integral_(- infinity)^(x_1) dots integral_(- infinity)^(x_n) P_arrow(xi) (t_1, t_2, dots, t_n) d t_n dots d t_1 $
]

#statement()[
  1. $xi_1, dots, xi_n$ --- независимые $<==>$ $F_arrow(xi) (arrow(x)) = F_(xi_1) (x_1) dot F_(xi_2) (x_2) dot dots dot F_(xi_n) (x_n) $
  2. $xi_1, dots, xi_n$ --- абсолютно непрерывны
  $xi_1, dots, xi_n$ --- независимы $<==>$ совместная плотность существует и $P_arrow(xi) (arrow(x)) = P_(xi_1) (x_1) dot dots dot P_(xi_n) (x_n)$
]

#remark()[
  По совместному распределению можно найти распределение любой компоненты.
  $ P_(xi_k) (B_k) = PP(xi_k in B_k) = PP(xi_1 in RR, dots, xi_(k - 1) in RR, xi_k in B_k, dots, xi_n in RR) = PP_arrow(xi) (RR^(k - 1) times B times RR^(n - k)) $

  В обратную сторону неверно $xi, eta in {0, 1}$ с вероятностью $1/2$. $angle.spheric (xi, eta)$:
  1. $xi = eta quad (xi, eta) in {(0, 0), (1, 1)}$ с вероятностью $1/2$
  2. $xi != eta quad (xi, eta) in {(1, 0), (0, 1)}$ с вероятностью $1/2$
]

= Численные характеристики случайный величин

#definition()[
  Математическое ожидание $EE_xi$
  $ EE xi = integral_Omega xi (omega) d PP(omega) $
]

#properties()[
  1. $EE xi$ --- линейно : $EE(a xi + b eta) = a EE xi + b EE eta$
  2. $xi >= 0$ с вероятностью $1$ $==>$ $EE xi >= 0$ (вместо $0$ можно любую константу)
  3. $xi >= eta$ с вероятностью $1$ $==>$ $EE xi >= EE eta$ (следует из двух предыдущих)
  4. $EE xi = integral_RR x d P_xi (x)$
  5. $EE f(xi_1, xi_2, dots, xi_n) = integral_(RR^n) f(t_1, dots, t_n) d P_arrow(xi) (t_1, dots, t_n)$, где $f$ --- измерима
  6. Если $xi$ и $eta$ --- независимы, то $EE xi eta = EE xi dot EE eta$
    #proof()[
      $ EE xi eta = integral_(R^2) x y d P_((xi, eta)) (x, y) = integral_(R^2) x y d P_xi (x) d P_eta (y) = integral_R x d P_xi (x) dot integral_R y d P_eta (y) = EE xi dot EE eta $
    ]
  7. Неравенство Гёльдера $p, q > 1 : 1/p  + 1/q = 1$
    $ EE |xi eta| <= (EE |xi|^p)^(1/p) dot (EE |eta|^q)^(1/q) $
  8. Неравенство Ляпунова $0 < r < s$
    $ (EE |xi|^r)^(1/r) <= (EE |xi|^s)^(1/s) $
    #proof()[
      $p = s/r > 1, q = p / (p - 1) quad 1 / p + (p - 1) / p = 1$
      $ EE |xi^r dot 1| <= (EE |xi^r|^(s / r))^(r / s) dot (EE |1|^q)^(1 / q) ==> EE |xi|^r <= (EE |xi|^s)^(r / s) $
    ]
  9. Неравенство Маркова $xi >= 0, t, p > 0$
    $ PP(xi >= t) <= (EE xi^p) / (t^p) $
    #proof()[
      $ EE xi^p = integral_RR x^p d P_xi (x) = integral_0^t x^p d P_xi (x) + integral_t^(+infinity) x^p d P_xi (x) >= integral_t^(+infinity) t^p d P_xi (x) = \
        = t^p dot integral_t^(+infinity) 1 dot d P_xi (x) = t^p dot PP(xi >= t)
      $
    ]
]

#definition()[
  *Медианой* случайной величины $xi$ называется $M in RR$: $PP(xi <= M) >= 1/2$ и $PP(xi >= M) >= 1/2$.
]

#definition()[
  *Дисперсией* случайной величины называется $DD xi = "Var" xi colon.eq EE (xi - E xi)^2$
]

#properties()[
  1. $DD xi = EE xi^2 - EE^2 xi$
    #proof()[
      $ EE (xi - EE xi)^2 = EE (xi^2 - 2 xi EE xi + EE^2 xi) = EE xi^2 - 2 EE xi dot EE xi + EE^2 xi = EE xi^2 - EE^2 xi $
    ]
  2. $DD (xi + a) = DD xi$
    #proof()[
        $ EE (xi + a - EE (xi + a))^2 = EE (xi - EE xi)^2 = DD xi $
    ]
  3. $DD (c xi) = c^2 DD xi$
    #proof()[
      $ EE (c xi - EE c xi)^2 = EE (c (xi - E xi))^2 = c^2 EE (xi - E xi)^2 = c^2 DD xi $
    ]
  4. $xi, eta$ --- независимы, то $DD (xi + eta) = DD xi + DD eta$
    #proof()[
      $ DD (xi + eta) = EE (xi + eta - EE xi - EE eta)^2 = EE ((xi - EE xi) + (eta - EE eta))^2 = \
      = EE ((xi - EE xi)^2 + (eta - EE eta)^2 - 2 (xi - EE xi) (eta - EE eta)) = DD xi + DD eta $
    ]
  5. $DD xi >= 0$ и $DD xi = 0 <==> $ $xi$ --- константа с вероятностью $1$
  6. $EE |xi - EE xi| <= sqrt(DD xi)$
    #proof()[Ляпунов.
      $EE |xi - EE xi| <= (EE |xi - EE xi|^2)^(1/2) = (DD xi)^(1/2)$
    ]
    $sqrt(DD xi) = sigma$ --- *стандартное отклонение*
  7. Неравенство Чернова $PP (|xi - EE xi| >= t) <= (DD xi) / t^2$
    #proof()[Неравенство Маркова для $p = 2$]
]
