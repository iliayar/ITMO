#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Лекция 6],
  date: [26 марта],
  number: 6,
  program: "ITMO MSE y2025",
  doc
)

= Дельта метод

- $X_1, dots, X_n$ --- н. о. р. $EE X_i = mu$, $DD X_i = sigma^2$
- $g(t) = a t + b$ и $Y_n = g(overline(X_n))$. 
$ EE Y_n = a mu + b = g(mu) quad DD Y_n = a^2 sigma^2 $

#theorem[
  $X_n$ --- последовательность с.в., $X$ --- с.в. Пусть для $b > 0 med exists a$:
  $ n^b (X_n - a) ->^d_(n -> +infinity) X $
  Пусть $exists g'(a) != 0$, тогда
  $ n^b (g(X_n) - g(a)) ->^d_(n -> +infinity) g'(a) X $
]

#corollary[
  $ sqrt(n) (overline(X_n) - mu) ->^d_(n -> +infinity) cal(N)(0, sigma^2) $
  #todo()
]
