#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 11],
  date: [26 ноября],
  number: 11,
  doc
)

#task(numbering: (..) => numbering("1", 1))[]
#solution()[
  Конечный второй момент: $EE xi^2$ --- конечная, т.е. $DD xi < +infinity$.

  $ DD S_n = o(n^2) ==> forall epsilon quad PP(|S_n / n - EE S_n / n| >= epsilon)-->0 $
  $ DD S_n / n = 1 / n^2 DD S_n = o(n^2) / n --> 0 $
  $ PP(|S_n / n - EE S_n / n| >= epsilon) <= #pin(1) (DD S_n / n) / epsilon^2 --> 0 $
  // FIXME
  // #pinit-point-from(1)[неравенство Чебышева]
]

#task(numbering: (..) => numbering("1", 2))[]
#solution()[
  $ EE xi = 0, EE xi^2 = 1, DD xi = 1$. $xi_k$ независимы и все
]

#task(numbering: (..) => numbering("1", 3))[]
#solution()[
  $EE xi_k = 0, EE xi_k^2 = 2^(2k)$. Нужно показать что $S_n / n -->^PP 0$, т.е. $PP(|S_n / n| > epsilon) --> 0$.
  $ S_n = plus.minus 2^n plus.minus 2^(n - 1) plus.minus dots plus.minus 2 $
  $ S'_n >= +2^n + underparen(2^(n - 1) - (2^(n - 2) + dots + 2), 2) $
  $ S''_n <= -2^n - 2 $

  $ {|S_n / n| > epsilon} supset {"sign" 2^n = "sing" 2^(n- 1)} $
  $ PP({|S_n / n| > epsilon}) >= PP({"sign" 2^n = "sing" 2^(n- 1)}) $
]

#task(numbering: (..) => numbering("1", 4))[]
#solution()[
  $X_L = {1, 0}$ --- попали/не попали на $L$-том выстреле. $p_L = 0.8 dot 0.99^(L - 1)$ попали на $L$ выстреле.

  $S_n = sum_(i = 0)^n X_i$ --- количество попавших выстрелов. 
  $ PP(|S_100 - EE S_100| >= delta) <= (DD S_100) / delta^2 $
  $ PP(|S_100 - EE S_100| <= delta) >= 1 - (DD S_100 / delta^2) $
  $ PP(- delta + EE S_100 < S_100 < EE S_100 + delta) >= 1 - (DD S_100) / delta^2 = 0.85 $

  $ EE S_100 = sum_(i = 1)^100 0.8 dot 0.99^(i - 1) dot 1 approx 50.72 $
  Потому что события независимые и ковариация $0$, $DD S_100 = sum DD S_i = sum p_i dot x_i^2 - (p_i dot x_i)^2 approx 22.87$
]

#task(numbering: (..) => numbering("1", 5))[]
#solution()[
  $ lim_(n -> +infinity) PP(a <= S_n <= b) = 0 $
  $ lim_(n -> +infinity) PP (overshell(a - mu_n, y_1) / sqrt(sigma^2 n) <= undershell((S_n - mu_n) / sqrt(sigma^2 n), eta) <= overshell(b - mu_b, y_2) / sqrt(sigma^2 n)) = F_(eta) (y_2) - F_(eta) (y_1) + overline(o)(1) =^? Phi(y_2) - Phi(y_1) + overline(o)(1) $
  1. $mu = 0$, $1/2 - 1/2 + 0 --> 0$
  1. $mu > 0$, $0 - 0 + 0 --> 0$
  1. $mu < 0$, $1 - 1 + 0 --> 0$

  Переход с впоросиком можем сделать потому что
  $ undershell((a_n - mu_m) / sqrt(sigma^2 n), eta) -->^d cal(N)(0, 1) $
  И получаем равномерную сходимость $F_eta (x) arrows Phi(x)$, т.е. $forall epsilon > 0 exists N : n >= N, forall x quad |F_eta(x) - Phi(x)| <= epsilon$
]

#task(numbering: (..) => numbering("1", 6))[]
#solution()[
  Пусть $eta_k = xi_k^2$.
  $EE xi_n = 0, DD xi_n = 1, EE xi_n^4 < +infinity$ значит $DD eta_i = DD xi_i^2 < +infinity$. По ЗБЧ:
  $ (eta_1 + dots + eta_n) / n -->^PP 1 $
  Возмем непрерывную функцию $f(x) = 1/x$:
  $ n / (eta_1 + dots + eta_n) -->^PP 1 ==> n / (xi_1^2 + dots + xi_n^2) --> 1 $
  по ЦПТ:
  $ (xi_1 + dots + xi_n - overshell(EE xi, 0)) / sqrt(n) -->^d cal(N)(0, 1) $
  По теореме Слуцкого перемножаем?
]

#task(numbering: (..) => numbering("1", 7))[]
#solution()[
  $PP(360 < #text[количество очков] < 430)$ --- ?. $X$ --- количество очков за один выстрел.

  // x | 10 | 9 | 8 | ... | 1
  // p | 1/100 | 3/100 | 5/100 | ... | 19/100

  $ S_n = sum_(i = 0)^n X_i $
  $ EE S_n = sum EE X_i quad EE X_i = 3.85 quad sqrt(DD X) = 2.351 $
  $ PP(360 < S_n < 430) = PP((360 - EE dot n) / sqrt(sigma^2 n) < (S_n - EE dot n) / sqrt(sigma^2 n) < (430 - EE dot n) / sqrt(sigma^2 n)) = Phi(dots) - Phi(dots) dots $
]

#task(numbering: (..) => numbering("1", 8))[]
#solution()[
  Пусть $xi_1, xi_2, dots$ --- н. о. р. с. в. с рапсределением Пуассона $"Pois"(1)$.
  $ PP(xi_i = k) = (e^(- lambda) dot lambda^k) / (k!) quad EE xi_i = lambda quad DD xi_i = lambda $
  $ S_n = sum xi_i $
  по ЦПТ
  $ (S_n - n) / sqrt(n) -->^d cal(N)(0, 1) $
  $ PP((S_n - n) / sqrt(n) <= 0) --> Phi(0) = 1/2 $
  $ PP((S_n - n) / sqrt(n) <= 0) = PP(xi_n <= n) = sum PP(S_n = k) = sum (e^(-n) n^k) / (k!) $
]
