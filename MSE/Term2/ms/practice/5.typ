#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 5],
  date: [19 марта],
  number: 5,
  doc
)

Доверительный интервал $forall theta in Theta$:
$ PP_theta (L_n(X_1, dots, X_n) <= theta <= R_n(X_1, dots, X_n)) = 1 - epsilon $
Либо
$ lim_(n -> infinity) PP_theta (L_n <= theta <= R_n) = 1 - epsilon) $

Рассмотрим $T(X_1, dots, X_n)$ --- $theta$
#example[
  $X_1, dots, X_n ~ U_([0, theta])$, то $X_((n)) / theta ~ max(Y_1, dots, Y_n)$, где $Y_i ~ U_([0, 1])$
  $ C(a, b) = PP(a <= X_((n)) / theta <= b) <==> PP(b / X_((n)) <= theta <= a / X_((n))) $
]

#task(numbering: (..) => numbering("1", 1))[
  - $X_1, dots, X_n ~ U_([0; theta])$
  - $T_n = 2 overline(X)$ для посторение ассимптотического интервала
  - $EE_theta [T_n] = 2 EE_theta [overline(X)] = 2 EE_theta [X_1] = 2 dot theta / 2 = theta$
  - $DD_theta [T_n] = 4 dot DD_theta[ overline(X)] = 4 dot DD_theta[X_1] / n = 4 dot theta^2 / 12n = theta^2 / 3n$
  $forall theta in Theta med T_n -->^(PP_theta) 2 dot theta / 2$ по ЗБЧ.
  По ЦПТ
  $ sqrt(n)(T_n - theta) ==> 2 sqrt(n) ((sum X_i) / n - theta /2 ) = 2 sqrt(n) ((sum (X_i - theta / 2)) / n) = \
    = 2 dot (sum_(i = 1)^n (X_i - theta / 2)) / sqrt(n) -->^d cal(N)(0, theta^2 / 3)
  $
  $ sqrt(n) (T_n - theta) / (theta / sqrt(3)) -->^d cal(N)(0, 1) $
  $ PP_theta (z_1 <= sqrt(n) (T_n - theta) / (theta / sqrt(3)) <= z_2 ) = Phi(z_2) - Phi(z_1) $
  $ z_1 = Phi^(-1)(epsilon / 2) = z_(epsilon / 2) = - z_(1 - epsilon / 2) quad z_2 = Phi^(-1)(1 -epsilon/2) = z_(1 - epsilon / 2) $
  $ PP_theta (z_(epsilon / 2) <= sqrt(n) (T_n - theta) / (theta / sqrt(3)) <= z_(1 - epsilon / 2)) = PP_theta (undershell(T_n / (1 + z_(1 - epsilon / 2) sqrt(1 / 3n)), L_n) <= theta <= undershell(T_n / (1 + z_(epsilon / 2) sqrt(1 / 3n)), R_n)) $
]

#remark[
  Нужно построить объект где фигурирует оценка $T_n$, параметр $theta$ и оно стремится к чему-то что от он $theta$ не зависит. 
]

#lemma("Слуцкого")[
  1. $xi_1, dots, xi_n -->^d xi_0$ --- сулчайная величина
  2. $eta_1, dots, eta_n -->^PP c$ --- константа
  то $f(xi_n, eta_n) -->^d f(xi_0, c)$ если $f$ непрерывна
]
#task(numbering: (..) => numbering("1", 2))[
  - $X_1, dots, X_n ~ B(p)$
  - $T_n = overline(X)$
  - $EE_p T_n = p$
  - $DD_p T_n = p(1-p) / n$
  По ЦПТ
  $ sqrt(n) (T_n - p) / sqrt(p (1 - p)) --> cal(N)(0, 1) $
  $ PP(z_(epsilon / 2) <= sqrt(n) (T_n - p) / sqrt(p (1 - p)) <= z_(1 - epsilon / 2)) --> 1 - epsilon $
  По лемме Слуцкого $xi_n = sqrt(n) (T_n - p) --> cal(N)(0, p(1 - p))$ по ЦПТ, $eta_n = sqrt(T_n (1 - T_n)) --> sqrt(p (1 - p))$ по ЗБЧ. $f(x, y) = x / y$.
  $ PP(z_(epsilon / 2) <= sqrt(n) (T_n - p) / sqrt(T_n (1 - T_n)) <= z_(1 - epsilon / 2)) --> 1 - epsilon $
  $ PP(T_n + z_(epsilon / 2) / sqrt(n) sqrt(T_n (1 - T_n)) <= p <= T_n + z_(1 - epsilon / 2) / sqrt(n) sqrt(T_n (1 - T_n))) $
]

#remark[
  - $xi_1 ~ cal(N)(mu, sigma^2)$, то $(xi_1 - mu_1) / sigma_1 ~ cal(N)(0, 1)$
  - $xi_1$ и $xi_2$ независимы. $xi_2 ~ cal(N)(mu_2, sigma_2^2)$, то $xi_1 + xi_2 ~ cal(N)(mu_1 + mu_2, sigma_1^2 + sigma_2^2)$
  - $xi_1, dots, xi_n ~ cal(N)(0, 1)$ независимы
    - $n overline(X^2) = sum_(i = 1)^n xi_1^2 ~ Chi^2(n) $
    $ f_(n overline(X^2)) = 1 / (2^(n / 2) Gamma(n / 2 - 1)) e^(- x / 2) x^(n / 2 - 1) $
    $Chi^2_alpha(n)$ --- число, такое что $ PP(n overline(X^2) <= Chi^2_alpha (n)) = alpha$
]

#task(numbering: (..) => numbering("1", 3))[
  $overline((X - a)^2) = 1/n sum_(i = 1)^n (X_i - a)^2$, где $X_i - a ~ cal(N)(0, sigma^2) = sigma cal(N)(0, 1)$ (т.к. $X_i ~ cal(N)(a, sigma^2)$.
  $ overline((X - a)^2) = 1 / n sum_(i = 1)^n (sigma (X_i - a) / sigma)^2 = sigma^2 / n sum_(i = 1)^n ((X_i - a) / sigma)^2 ~ sigma^2 / n Chi^2 (n) $
  $n dot overline((X - a)^2) / sigma^2 ~ Chi^2 (n)$, а значит
  $ PP(Chi^2_(epsilon / 2) (n) <= n dot overline((X - a)^2) / sigma^2 <= Chi^2_(1 - epsilon / 2) (n)) = 1 - epsilon $
  $ PP((n overline((X - a)^2)) / (Chi^2_(1 - epsilon / 2) (n)) <= sigma^2 <= (n overline((X - a)^2)) / (Chi^2_(epsilon / 2) (n))) = 1 - epsilon $
]

#task(numbering: (..) => numbering("1", 3))[
  $T = (overline(X) - a)^2$. $overline(X) ~ cal(N)(a, sigma^2 / n) ==> overline(X) - a ~ cal(N)(0, sigma^2 / n)$, $overline(X) - a ~ sigma / sqrt(n) cal(N)(0, 1)$, $(overline(X) - a)^2 ~ sigma^2 / n Chi^2 (1)$.
  $ PP(Chi^2_(epsilon / 2) <= (n (overline(X) - a)^2) / sigma^2 <= Chi^2_(1 - epsilon / 2) (1) ) = 1 - epsilon $
  $ PP((n (overline(X) - a)^2) / (Chi^2_(1 - epsilon / 2) (1)) <= sigma^2 <= (n (overline(X) - a)^2) / (Chi^2_(epsilon / 2) (1))) = 1 - epsilon $
]
