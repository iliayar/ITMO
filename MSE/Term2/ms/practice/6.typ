#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 6],
  date: [26 марта],
  number: 6,
  doc
)

#remark[
  $xi$ --- с. в.
  $ EE [f(xi)] = integral_RR x p_(f(xi)) (x) d x = integral_RR f(x) p_xi (x) d x $
  $ DD xi = integral_RR (x - EE xi)^2 d x $
]
#remark[
  Вообще говоря неверно что $EE [f(xi)] = f(EE xi)$, но $EE [f(xi)] approx f(EE xi)$. Пусть $EE xi = mu$
  $ f(xi) approx f(mu) + f'(mu)(xi - mu) $
  $ EE [f(xi)] approx EE xi + f'(mu) undershell(EE [xi - mu], 0) $
  $ DD [f(xi)] approx EE[(f(xi) - f(mu))^2] approx EE [(f'(mu) (xi - mu))^2] = (f' (mu))^2 DD xi $
]

#task[
  Точно:
  $ EE [1/X] = integral_10^20 1/x dot 1/10 d x = lr(1/10 ln x|)_10^20 = 1/10 ln 20 / 10= 1/10 ln 2 approx 0.069 $

  $ PP(1/x <= t) = PP(x >= 1 / t) = 1 - PP(x < 1/t) = 1 - (1/t - 10) / (20 - 10) = 2 - 1/(10 t) $
  $ PP_(1/X) (t) = EE 1/x = integral_(1/20)^(1/10) t dot 1/(10t^2) = (ln 1/10 - ln 1/20) / 10 = (ln 2) / 10 $
  $ EE 1/x^2 = integral_(1 / 20)^(1/ 10) = t^2 dot 1 / (10 t^2) d t = 1/10 (1/10 - 1/20) = 1/200 $
  $ DD X = 1/200 - (ln^2 2) / 100 $

  Примерно:
  $ EE [1/X] approx 1/(EE X) = 1 / ((20 + 10) / 2) = 1/15 approx 0.066 $
  $ f(x) = 1/x quad f'(x) = -1/x^2 $
  $ DD [1/X] = 1 / 15^4 dot (10^2) / 12 = 1/(35 dot 25)$
]

#remark[
  $ xi_n ->^PP xi ==> f(xi_n) ->^PP f(xi) $
  --- теорема Слуцкого. Делта-метод
  $ hat(theta)_n = f(x_1, dots, x_n) $
  $ sqrt(n) (hat(theta)_n - theta) ->^d cal(N)(0, sigma^2 (theta)) $
  Тогда $forall g$ --- "хорошей"
  $ sqrt(n) (g(hat(theta)_n) - g(theta)) ->^d cal(N) (0, sigma^2 (theta) dot (g'(theta))^2) $
]

#task[
  - $X_1, dots, X_n ~ U[l; theta]$
  - $hat(theta)_(n, k) = root(4, (k + 1) / n sum_(i = 1)^n X_i^k)$
  
  1. Доказать что $forall theta$:
    $ sqrt(n) (hat(theta)_(n, k) - theta) ->^d cal(N) (0, sigma^2 (theta)) $
  2. Найти $sigma^2 (theta)$

  - $g(x) = root(k, (k + 1) x)$

  Из оценки $hat(theta)_(n, k)$ получаем $theta = (theta^k) / (k + 1)$
  $ EE [X_1^k] = theta^k / (k + 1) quad DD [X_1^k] = theta^(2 k) / (2k + 1) - theta^(2k) / (k + 1)^2 = (theta^(2k) k^2) / ((2k + 1) (k + 1)^2) $
  По ЦПТ
  $ sqrt(n) (overline(X^k) - EE_theta [X_1^k]) ->^d cal(N)(0, DD_theta [X_1^k]) $
  Делта-метод:
  $ sqrt(n) (g(overline(X^k)) - g(theta^k / (k + 1))) -> cal(N)(0, (theta^(2k) k^2) / ((2k + 1) (k + 1)^2) (k+1)^2 / k^2 dot 1 / theta^(2k - 2)) $
]

#task[
  #todo()
]
