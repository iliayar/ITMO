#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 4],
  date: [12 марта],
  number: 4,
  doc
)

#remark[
  $X_1, dots, X_n$ --- выборка. Плотность/Функция вероятности $f(x | theta)$, где $theta$ --- параметр (постоянно значный, неизвестный).

  $ cal(L)_n (theta) = product_(i = 1)^n f(X_i | theta) $
  $ hat(theta)^#text[ОМП]_n = "argmax"_theta cal(L)_n (theta) = "argmax"_theta l_n (theta) $
  $ l_n (theta) = ln cal(L)_n (theta) = sum_(i = 1)^n ln f (X_i | theta) $
  $cal(L)$ это функция правдопобия, $l$ --- логирафмическа функция правдоподобия
]

#task(numbering: (..) => numbering("1.a", 1, 1))[
  $X_1,dots,X-n ~ "Poiss"(theta)$.
  $ f(k | theta) = PP_theta (X_i = k) = theta^k / k! e^(-theta) $
  $ cal(L)_n (theta) = product_(i = 1)^n theta^(X_i) / (X_i !) e^(-theta) = theta^(sum_(i = 1)^n X_i e^(-n theta)) / (product_(i = 1)^n X_i !) $
  $ l_n (theta) = (sum_(i = 1)^n X_i) dot ln theta - n theta - ln product_(i = 1)^n X_i ! $
  $ l'_n (theta) = 1 / theta sum_(i = 1)^n X_i - n quad l'_n (hat(theta)^#text[ОМП]) = 0 \
    1 / hat(theta) sum_(i = 1)^n X_i - n = 0 ==> hat(theta) = (sum_(i = 1)^n X_i) / n = overline(X)
  $
  Не факт что максимум или минимум. Продифириенцируем второй раз
  $ l''_n (theta) = - 1 / theta^2 sum_(i = 1)^n X_i $
  Рассмотрим два варианта:
  - $sum X_i > 0$, тогда $l''_n < 0$, а значит находимся в точке локального максиума
  - $sum X_i = 0$, т.е. все $X_i = 0$.
]

#task(numbering: (..) => numbering("1.a", 1, 3))[
  $ f(x | theta) = 1 / 2 e^(-|x - theta|) quad ln f(x | theta) = - |X_i - theta| - ln 2 $
  $ cal(L)_n (theta) = product_(i = 1)^n 1 / 2 e^(-|X_i - theta|)  $
  $ l_n (theta) = - sum_(i = 1)^n |X_i - theta| - n ln 2 $
  Рассмотрим $Z(theta) = sum_(i = 1)^n |X_i - theta|$.
  $ Z'(theta) = sum_(i = 1)^n "sign"(theta - X_i) $
  Получаем корыто. Тогда при нечетном $n$ $hat(theta) = X_((n + 1 / 2))$  --- $(n + 1) / 2$-я порядковая статистика. Когда $n$ четно $hat(theta) in [ X_((n / 2)); X_((n / 2 + 1)) ]$.

  В итоге $l_n (theta) ->_theta max <==> Z ->_theta min$
]

#task(numbering: (..) => numbering("1.a", 1, 4))[
  $cal(N)(mu, sigma^2)$
  $ f(x | mu, sigma^2) = 1 / sqrt(2 pi sqrt^2) e^(-(x-mu)^2 / (2 sigma^2)) quad ln f(x, mu, sigma^2) = - (x - mu)^2 / (2 sigma^2) - 1/2 ln sigma^2 - 1/2 ln (2 pi) $
  $ l_n (mu, sigma^2) = sum_(i = 1)^n ln f(X_i | mu, sigma^2) -> max <==> 1 / (2 sigma^2) sum_(i = 1)^n (X_i - mu)^2 + n / 2ln sigma^2 -> min $
  Пусть $sigma^2$ известно. Хотим $sum_(i = 1)^n (X_i - mu)^2 -> min$. Уравнение на 
  $ sum_(i = 1)^n 2 (X_i - hat(mu)) = 0 ==> sum_(i = 1)^n X_i = n hat(mu) ==> hat(mu) = overline(X) $

  Теперь на другую переменную:
  $ - 1 / (2 (hat(sigma)^2)^2) sum_(i = 1)^n (X_i - hat(mu))^2 + n / (2 hat(sigma)^2) = 0 => \
    => 1 / hat(sigma)^2 sum_(i = 1)^n (X_i - hat(mu))^2 => hat(sigma)^2 = 1/n sum_(i = 1)^n (X_i - hat(mu))^2
  $
]

#task(numbering: (..) => numbering("1", 2))[
  Неравенство Рао-Крамера
  $ EE_theta [ (hat(theta) - theta)^2 ] >= (1 + b' (theta))^2 / (n I_1 (theta)) + b^2 (theta) $
  где $b(theta) = EE_theta [ theta - hat(theta) ]$, $I$ --- информация Фишера (?)
  $hat(theta) = overline(X) = 1/n sum_(i = 1)^n X_i$. $X_i ~ "Poiss"(theta)$, $EE X_i = theta$, $DD X_i = theta$ $==>$ $EE_theta hat(theta) = theta$ т.е. оценка несмещенная
  $ DD_theta [hat(theta)] = 1 / (n dot I_1 (theta) \
    DD_theta [hat(theta)] = DD X_1 / n = theta / n \
    I_1 (theta) = EE_theta [partial / (partial theta) ln ((e^(-theta) theta^(X_1)) / (X_1 !))^2]
  $
  $ partial / (partial theta) ln ((e^(-theta) theta^(X_1)) / (X_1 !))^2 = partial / (partial theta) (-theta + X_1 ln theta - ln X_1 !) = -1 + X_1 / theta = (X_1 - theta) / theta $
  Тогда $ DD_theta [hat(theta)] = 1 / (n dot 1/theta) = theta / n $
]
