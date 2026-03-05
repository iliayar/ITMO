#import "common.typ": *

#show: doc => practice(
  subj: [Математическая Статистика],
  title: [Практика 3],
  date: [5 марта],
  number: 3,
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  - $X_1, dots, X_n ~ U[0; theta]$
  - Построить $hat(theta)_n^((k))$ методом моментов
  - Оценить $EE_theta [(hat(theta)_n^((k)) - theta)^2] approx ?$
]
#solution[
  $ overline(X) = 1/n (X_1 + dots + X_n) $
  $ EE_theta [g(X_1)] approx 1/n sum_(i = 1)^n g(X_i) #text[уравнение на theta] \
    EE_theta[X_1^k] = 1/n sum_(i = 1)%n X_i^k = overline(X)^k #text[решаем ур-е получаем оцегку метод] \
    = integral_0^theta x^k 1/theta d x = x^(k + 1) / (theta (k + 1)) |_(x= 0)^(x = theta) = theta^k / (k + 1)
  $
  $ (hat(theta)_n^((k)))^k / (k + 1) =11 / n sum_(i = 1)^n X_i^k = overline(X)^k => hat(theta)_n^((k)) = root(4, (k + 1) overline(X)^k) = \
    = root(k, (k + 1) / n sum_(i = 1)^n X_i^k)
  $
  $ EE_theta [(root(k, (k + 1) / n sum_(i = 1)^n X_i^k) - theta)^2] = EE_theta [(f(overline(X)^k - f(a_theta)^2] $
  $ f(overline(X)^k) - f(a_theta) approx f'(a_theta)(overline(X)^k - a_theta) + o(overline(X)^k - a_theta) $
  Это ряд Тейлора
  $ EE_theta approx ((k + 1) / (k theta^(k - 1))^2 EE_theta [(overline(X)^k - a_theta)^2] = dots $
]

#task(numbering: (..) => numbering("1", 1))[
  - $X_1, dots, X_n ~ "Exp"(lambda) = 1 / lambda "Exp"(1)$
  - $f_(X_i) (x) = lambda e^(- lambda x) bb(1){x >= 0}$

  1. Построить $hat(theta)_n^((k))$ методом моментов с $g(x) = x^k$
  2. Оценить ее СКО

  1. Найти $EE_lambda [X_1^k]$
  2. Записать и решить уравнение на $lambda_n^((k))$
  3. Представить СКО в виде $E_lambda [(f(overline(X)^k) - f(EE_lambda [x_1^k]))^2]$
  4. Расписать в ряд и упростить
]
#remark[
  Забавные факты
  $ EE[h(x)] = integral_RR h(x) f_X (x) d x $
  $ integral_0^infinity x^k e^(- x) d x = Gamma(k + 1) = k! $
]
#remark[
  СКО
  - $EE_theta [(hat(theta) - theta)^2]$
]
#solution[
  1.
    $ EE_lambda[X_1^k] = integral_0^infinity lambda x^k e^(-lambda x) d x = k! / lambda^k $
    $ k! / (hat(lambda)_n^((k)))^k = overline(X)^k ==> hat(lambda)_n^((k)) = root(k, k! / overline(X)^k) $
    Или $hat(theta)_n^((k)) = root(k, overline(X)^k / k!)$

    $ f(x) = (k! / x)^(1 / k) = (x / k!)^(- 1 / k) ==> f'(x) = - 1 / k dot 1 /k! dot (x / k!)^(-1/k - 1) $
    $ E_lambda ((hat(theta)^((k))_n - theta)^2) approx (f'(k! /  lambda^k))^2 undershell(EE_lambda [(overline(X)^k - k! / lambda^k)^2], DD_lambda[overline(X)^k]) =\
      1 / k^2 dot lambda^(2k + 2) / (k!)^2 dot ((2 k)! / lambda^(2k) - (k!)^2 / lambda^(2k)) dot 1/ n
    $
]
