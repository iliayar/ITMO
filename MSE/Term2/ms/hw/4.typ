#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 1, 1))[]
#solution[
  $ cal(L)(theta) = product_(i = 1)^n theta X_i^(theta - 1) $
  $ cal(l)(theta) = sum_(i = 1)^n ln theta + (theta - i) ln X_i = n ln theta + (theta - 1) sum_(i = 1)^n ln X_i $
  $ cal(l)'(theta) = n / theta + sum_(i = 1)^n ln X_i = 0 ==> hat(theta) = - n / (sum_(i = 1)^n ln X_i) $

  $cal(l)''(theta) = - n / theta^2 < 0$, а значит $hat(theta)$ это точка максимума
]

#task(numbering: (..) => numbering("1.a", 1, 2))[]
#solution[
  $ cal(L)(theta) = product_(i = 1)^n (2 X) / theta^2 $
  Можно сразу заметить что $cal(L)$ убывает на промежутке $[0; theta]$. Значит максимум достигается при наименьшем возможном $theta$ и при этом $cal(L)(theta) > 0$. То есть нужно чтобы для всех $X_i$ было $f(X_i | theta) > 0$. Для этого требуется чтобы $forall i med X_i in [0; theta]$. Значит наименьшний подходящий $hat(theta) = max X_i$.
]

#task(numbering: (..) => numbering("1.a", 1, 3))[]
#solution[
  $ cal(L)(theta) = product_(i = 1)^n (e^(-|X|)) / (2 (1 - e^(-theta))) $
  Аналогично: $e^(-theta)$ убывает по $theta$, $1 - e^(-theta)$ возрастает по $theta$ и тогда вся $f(X_i | theta)$ убывает по $theta$. Значит нужно взять наименьшее подходящее $theta$. Это будет $hat(theta) = max |X_i|$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  $ cal(L)(alpha, beta) = product_(i = 1)^n alpha^(-1) e^(- (X_i - beta) / alpha) $
  Заметим что $f(X | alpha, beta)$ возрастает по $beta$. Значит максимум по $beta$ с учетом ограничений будет достигаться при $hat(beta) = min X_i$. Теперь найдем точку максимума по $alpha$:
  $ cal(l)(alpha) = sum_(i = 1)^n - ln alpha - (X_i - beta) / alpha = - n ln alpha - ((sum_(i = 1)^n X_i) - n beta) / alpha $
  $ cal(l)'(alpha) = - n /alpha + ((sum_(i = 1)^n X_i) - n beta) / alpha^2 = 0 ==> hat(alpha) = overline(X) - hat(beta) = overline(X) - min X_i $
  Это _скорее всего_ максимум. Получается максимум в точке $(overline(X) - min X_i, min X_i)$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution[
  Известно что для нормального распределения $hat(theta) = overline(X)$.
  $EE hat(theta) = EE overline(X) = 1/n dot n EE X = theta$ --- значит оценка несмещенная. Т.к. $X_i$ независимы, то можем посчитать $DD hat(theta)$:
  $ DD hat(theta) = DD overline(X) = 1/n^2 sum_(i = 1)^n DD X_i = sigma^2 / n $
  Посчитаем $I_1 (theta)$:
  $ partial / (partial theta) ln (1 / (sqrt(2 pi) sigma) e^(-1/2 ((X_1 - theta) / sigma)^2)) = partial / (partial theta) (-1/2 ln (2pi) - ln sigma - 1/2 ((X_1 - theta) / sigma)^2) = (X_1 - theta) / sigma^2  $
  $ I_1 (theta) = EE (partial / (partial theta) ln (1 / (sqrt(2 pi) sigma) e^(-1/2 ((X_1 - theta) / sigma)^2)))^2 = EE ((X_1 - theta) / sigma^2)^2 = 1 / sigma^4 EE (X_1 - theta)^2 = \
    = 1 / sigma^4 EE (X_1 - EE X_1)^2 = 1 / sigma^4 DD X_1 = 1 / sigma^2
  $
  Тогда в неравенстве Рао-Крамера достигается равенство:
  $ DD hat(theta) = sigma^2 / n = 1 / (n I_1 theta) $
  Значит оценка $theta$ является R-эффективной
]
