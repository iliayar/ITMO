#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 8],
  date: [29 октября],
  number: 8,
  doc
)

#task()[]
#solution()[
  $X in {0, 1, 2}$
  $ F_X(x) = P(X <= x) $
  $ F(x) = cases(
    0 quad & ","x < 0,
    binom(25, 2) / binom(30, 2) quad & "," 0 <= x < 1,
    (binom(25, 2) + binom(25, 1) dot binom(5, 1)) / binom(30, 2) quad & "," 1 <= x < 2,
    1 quad & "," x >= 2
  ) $

  $ EE X = sum_a a dot p(a) quad DD X = EE X^2 - (EE X)^2 $
  $ EE X  = 0 dot binom(25, 2) / binom(30, 2) + 1 dot (binom(25, 1) dot binom(5, 1)) / binom(30, 2) + 2 dot binom(5, 2) / binom(30, 2) $
  $ EE X^2 = 0 dot binom(25, 2) / binom(30, 2) + 1 dot (binom(25, 1) dot binom(5, 1)) / binom(30, 2) + 4 dot binom(5, 2) / binom(30, 2) $
]

#task()[]
#solution()[
  $ integral_(-infinity)^(+infinity) f(x) d x = 1$
  $ 1 = integral_0^2 a x^2 d x = lr(a x^3 / 3 bar)_0^2 = a dot 8 / 3 = 1 ==> a = 3 / 8 $
  $ PP(x > 1) = 1 - PP(x <= 1) = 1 - F(1) $
  $ F(x) = integral_(-infinity)^x f(x) d x $
]

#task()[]
#solution()[
  $ F(x) = integral_3^x (7 - t) / 8 d t = (-x^2 + 14 x - 33) / 16 $
  $ F(x) = cases(
    0 quad & "," x < 3,
    (-x^2 + 14 x - 33) / 16 quad & "," 3 <= x <= 7
    0 quad & "," x > 7,
  ) $
  $ PP(2 <= x <= 4) = F(4) - F(2) $
  $ EE X = integral_(- infinity)^(+infinity) x f(x) d x $
  $ EE X = integral_3^7 x dot (7 - x) / 8 d x = dots = 13 /3 $
  $ DD X = EE X^2 - (EE X)^2 = integral_3^7 x^2 (7 - x) / 8 d x - (integral_3^7 x (7 - x) / 8 d x)^2 = 8 / 9 $
]

#task()[
  #align(center)[
    #table(
      columns: 6,
      $X$, $0$ , $pi / 6$, $pi / 2$, $(5 pi) / 6$, $pi$,
      $PP$, $0.1$, $0.3$, $0.1$, $0.2$, $0.3$
    )
  ]
]
#solution()[
  $ PP(Y = 0) = 0.4 quad PP(Y = 1/2) = 0.5 quad PP(Y = 1) = 0.1$
  $ F(x) = cases(
      0 quad & "," x < 0,
      0.4 quad & "," 0 <= x < 1 / 2,
      0.9 quad & "," 1 / 2 <= x < 1 ,
      1 quad & "," x >= 1
  ) $
]

#task()[]
#solution()[
  $ tilde(F) (x) = PP(X_((k)) <= x) $
  $mu_n (x)$ --- количество значений которые $<= x$. Тогда 
  $ PP(X_((k)) <= x) = PP(mu_n (x) >= k) = PP(mu_n (x) = k) + PP(mu_n (x) = k + 1) + dots + PP(mu_n (x) = n) $
  $ PP(mu_n (x) = k) = binom(n, k) underbrace(PP(X_((i)) <= x)^k, F(x)) dot (1 - underbrace(PP(X_((i)) <= x), F(x)))^(n - k) = \
    = binom(n, k) F(x)^k (1 - F(x))^(n - k)
  $
  $ tilde(F)(x) = sum_(i = k)^n binom(n, i) F(x)^i (1 - F(x))^(n - i) $

  $ tilde(F)(x) = sum_(i = k)^n binom(n, i) (F(x)^i dot (n - 1) dot (1 - F(x))^(n - i - 1) dot (- F'(x)) + i dot F(x)^(i - 1) dot F'(x) dot (1 - F(x))^(n - i)) = \
    = p(x) dot n dot binom(n - 1, k - 1) F^(k - 1) (x) dot (1 - F(x))^(n - k)
  $
]
