#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution[
  Заметим что $X_((1)) = min(X_1, dots, X_n)$. Тогда, учитывая что с.в. независимы:
  $ F_(X_((1)))(x) & = PP(X_((1)) <= x) = PP(min(X_1, dots, X_n) <= x) = 1 - PP(min(X_1, dots, X_n) >= x) = \
    & = 1 - PP(X_1 >= x, dots, X_n >= x) = 1 - product_(i = 1)^n PP(X_i >= x) = 1 - product_(i = 1)^n (1 - F(x)) = \
    & = 1 - (1 - F(x))^n
  $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Знаем что функция распределния $X_((1))$ это $F_(X_((1))) = 1 - (1 - F(x))^n$, где $F'(x) = f(x)$. Значит
  $ f_(X_((1))) & = F'_(X_((1))) = -n (1 - F(x))^(n - 1) dot (1 - F(x))' = \
    & = n (1 - F(x))^(n - 1) dot f(x)
  $
  где $F(x) = integral_(-infinity)^x f(x) d x$
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 3, 1))[]
#solution[
  Равное распределение, значит $PP(X_i < x) = x / theta$. Уже знаем что
  $ F_(X_((1))) = 1 - product_(i = 1)^n (1 - F_(X_i)) = 1 - (1 - x / theta)^n $
  Значит $f_(X_((1))) = F'_(X_((1))) = n / theta (1 - x / theta)^(n - 1)$
  $ EE (n + 1) X_((1)) = integral_0^theta x f_(X_((1))) d x = n / theta integral_0^theta x (1 - x/ theta)^(n - 1) d x = theta / (n + 1) $
  Тогда $EE (n + 1) X_((1)) = theta$. Значит оценка *несмещенная*.

  Возьмем $epsilon = theta / 2$. Тогда
  $ PP(|(n + 1) X_((1)) - theta| < theta / 2) = PP(theta / 2 < (n + 1)X_((1)) < 3/2 theta) = PP(X_((1)) > theta / (2 (n + 1))) = \
    = 1 - PP(X_((1)) < theta / (2 (n + 1))) = (1 - 1 / (2 (n + 1)))^n ->_(n -> +infinity) e^(-1/2)
  $
  Тогда $PP(|(n + 1) X_((1)) - theta| > theta / 2) = 1 - e^(-1/2) != 0$. Значит оценка *несостоятельная*
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.a", 3, 2))[]
#solution[
  Аналогично:
  $ EE (X_((1)) + X_((n))) = theta / (n + 1) + (n theta) / (n + 1) = theta $
  Значит оценка *несмещенная*.

  Возьмем произовольное $epsilon$.
  $ PP(|X_((1)) + X_((n)) - theta| > epsilon) = PP(X_((1)) + (theta - X_((n))) > epsilon) <= PP(X_((1)) > epsilon / 2) + PP(theta - X_((n)) > epsilon / 2) $
  Но $PP(X_((1)) > epsilon / 2) = (1 - epsilon / (2 theta)) ->_(n -> +infinity) 0$ и
  $ PP(theta - X_((n)) > epsilon / 2) = PP(X_((n)) < theta - epsilon / 2) = ((theta - epsilon / 2) / theta)^n = (1 - epsilon / (2 theta))^n ->_(n -> +infinity) 0 $
  Значит правая часть неравества $PP(X_((1)) > epsilon / 2) + PP(theta - X_((n)) > epsilon / 2) ->_(n -> +infinity) 0$ и оценка *состоятельная*
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 4))[]
#solution[
  Известно#footnote[#link("https://ru.wikipedia.org/wiki/Экспоненциальное_распределение#Связь_с_другими_распределениями")] что $sum_(i = 1)^n X_i$, где $X_i ~ "Exp"(lambda)$, имеем распределение $Gamma(n, 1/lambda)$. Тогда $f_(sum X_i) (x) = x^(n - 1) lambda^n e^(-lambda x) / (n - 1)! bb(1)_([0; +infinity)) (x)$. Тогда можем посчитать $EE(n / (sum X_i))$ через плотность:
  $ EE (n / (sum X_i)) = n dot integral_0^infinity 1 / x dot x^(n - 1) lambda^n e^(-lambda x) / (n - 1)! d x = (n lambda^n) / (n - 1)! integral_0^infinity x^(n - 2) e^(- lambda x) d x = \
    = (n lambda^n) / (n - 1)! dot (n - 2)! / lambda^(n - 1) = (lambda n) / (n - 1) != lambda
  $
  Значит $1 / overline(X)$ *смещенная* (но видимо ассимптотически несмещенная, т.к. $EE 1 / overline(X) ->_(n -> +infinity) lambda$).

  По ЗБЧ $overline(X) ->^PP EE X_i = 1 / lambda$, т.к. $DD X_i = 2/lambda^2$. Значит $1 / overline(X) ->^PP lambda$. Значит оценка *состоятельная*
]
