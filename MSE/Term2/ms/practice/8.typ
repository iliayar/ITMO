#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 8],
  date: [23 апреля],
  number: 8,
  doc
)

#remark[
  - $X_1, dots, X_n ~ cal(N)(mu, sigma^2)$

  - $H_0 : mu = mu_0$
  - $H_1 : mu != mu_0$
  Смотрим насколько прадоподобна выборка при $H_0$.

  - $sigma^2$ известна. $z$-тест
    - $Z = sqrt(n) (overline(X) - mu_0) / sigma ~_(H_0) cal(N)(0, 1)$
    - $Z in [z_(alpha / 2), z_(1 - alpha / 2)]$ --- не отклоняем $H_0$
    - $Z in.not [z_(alpha / 2), z_(1 - alpha / 2)]$ --- отклоняем $H_0$

    Если $H_1 : mu > mu_0$, то если $Z < z_(1 - alpha)$ --- принять $H_0$.
  - $sigma^2$ не известно. $t$-тест
    - $T = sqrt(n) (overline(X) - mu_0) / sqrt(s^2) ~_(H_0) t(n - 1)$
      где
      $ s^2 = 1 / (n - 1) sum_(i = 1)^n (X_i - overline(X))^2 $ --- исправленное среднекадратичное отклонение
    - $T in [t_(alpha / 2) (n - 1), t_(1 - alpha / 2) (n - 1)]$ --- не отклоняем $H_0$
    - $T in.not [t_(alpha / 2) (n - 1), t_(1 - alpha / 2) (n - 1)]$ --- отклоняем $H_0$
  - Проверка дисперсии. Тест Фишера
    $ chi^2 = ((n - 1) s^2) / sigma^2_0 ~ chi^2 (n - 1) $, где $ s^2 = 1 / (n - 1) sum_(i = 1)^n (X_i - overline(X))^2 $
    - $H_0: sigma^2 = sigma^2_0$
    1. $H_1: sigma^2 != sigma^2_0$
    2. $H_1: sigma^2 < sigma^2_0$
    3. $H_1: sigma^2 > sigma^2_0$
    Тогда не отклоняем $H_0$
    1. $chi^2 in [chi^2_(alpha / 2) (n - 1); xi^2_(1 - alpha / 2) (n - 1)]$
    2. $chi^2 < chi^2_(1 - alpha) (n - 1)$
    3. $chi^2 > chi^2(alpha) (n - 1)$
]

#task[
   - $Z = sqrt(n) (overline(X) - a) / sigma = sqrt(100) (26.5 - 25) / 5 = 3$
   - $z(alpha / 2) = z_(0.025) = = -Phi(1 - 0.025) = -Phi(0.9750) = -1.96$
   - $z_(1 - alpha / 2) = z_(1 - 0.025) = Phi(0.9750) = 1.96$
   - $3 in.not [-1.96, 1.96]$ --- отклоняем $H_0$.

   Теперь когда $H_1 : Z < z_(1 - alpha)$.
   - $z_(1 - alpha) = z_(0.950) = Phi(0.950) approx 1.645 $
]

#task[
  - $T = sqrt(16) (overline(X) - a) / s = (12.4 - 11.8) / 1.2 = 0.5 $
  - $t^(16 - 1)_(0.05) = - t^15_(1 - 0.05) = -t^15_(0.95) approx  = -1.753 < 0.57 $
  - Не отклоняем $H_0$.
]

#task[
  - $xi^2 = (24 - 0.02) / 0.03 = 48$
  - $xi^2_(0.95) (24) = 36.4$
  - $48 > 36.4$ --- отвергаем $H_0$.
]
