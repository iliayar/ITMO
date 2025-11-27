#import "common.typ": *

#show: doc => hw(11, doc)

#line(length: 100%)
#task()[]
#solution()[
  $ EE xi_k = - 2^k dot 2^(-2k - 1) - 1 dot (1 - 2^(-2k)) / 2 + 1 dot (1 - 2^(-2k)) / 2 + 2^k dot 2^(-2k - 1) = 0 $
  $ EE xi^2_k = 2^(2k) dot 2^(-2k - 1) + 1 dot (1 - 2^(-2k)) / 2 + 1 dot (1 - 2^(-2k)) / 2 + 2^(2k) dot 2^(-2k - 1) = 2 - 2^(-2k) <= 2 $
  Значит $ DD xi_k = 2 - 2^(-2k) - 0^2 <= 2$. По условию ${xi_k}$ независимые, значит ЗБЧ выполняется.
]

#line(length: 100%)
#task()[]
#solution()[
  Пусть $xi_k = "Pois"(250)$ --- число пришедших пассажиров, а $eta_k in [195; 205]$ --- число уехавших. Видимо $xi_k$ и $eta_k$ независимые. Пусть $delta_k = xi_k - eta_k$, т.е. изменение количества пассажиров на перроне.
  $ EE delta_k = EE xi_k - EE eta_k = lambda - (sum_(x = 195)^205 x) / (205 - 195 + 1) = 250 - 200 = 50 $
  $ DD delta_k = DD xi_k + DD eta_k = lambda + ((sum_(x = 195)^205 x^2) / (205 - 195 + 1) - 200^2) = 250 + 10 = 260 $
  Тогда $S_n = sum_(k = 1)^n delta_k$ --- изменение количества людей на пероне после $n$ интервалов.
  $ EE S_n = sum_(k = 1)^n EE delta_k = 50 n quad DD S_n = sum_(k = 1)^n DD delta_k = 260 n $

  Посчитаем вероятность того что перрон не переполнится по неравенству Чебышева:
  $ PP(S_n <= N) = PP(-S_n + EE S_n >= - N + EE S_n) = \
    = PP(|- S_n + EE S_n| >= EE S_n - N) = PP(|S_n - EE S_n| >= EE S_n - N)
  $
  $ PP(|S_n - 50n| >= 50n - N) <= (DD S_n) / (50n - N)^2 = (260n) / (2500n^2 - 100 n N + N^2) -->_(n --> infinity) 0 $
  Получается что вероятность того что перрон не переполнится стремится к $0$, а значит он почти наверняка переполнится.
]

#line(length: 100%)
#task()[]
#solution()[
  Пусть $xi_k$ --- число на кубике на $k$-том броске.
  $ EE xi_k = (sum_(i = 1)^6 x) / 6 = 7 / 2 quad EE xi^2_k = (sum_(i = 1)^6 x^2) / 6 = 91/6 $
  $ DD xi_k = 91/6 - (7/2)^2 = 35 / 12 $
  Пусть $S_n = sum_(k = 1)^n xi_k$ --- сумма чисел после $n$ бросков. Можем применить ЦПТ:
  #enum(numbering: (..ns) => numbering("a)", ..ns))[
    $PP(S_210 <= 700)$ --- вероятность того что потребуется больше $210$ бросков чтобы набрать $700$.
    $ PP(S_210 <= 700) = PP((S_210 - 210 dot 91 / 6) / sqrt(210 dot 35 / 12) <= (700 - 210 dot 91 / 6) / sqrt(210 dot 35 / 12)) --> Phi((700 - 210 dot 91 / 6) / sqrt(210 dot 35 / 12)) = \
      = Phi(- sqrt(2)) approx 0.07865
    $
  ][
    $PP(S_180 > 700)$ --- вероятность того что потребуется меньше чем $180$ бросков чтобы набрать $700$.
    $ PP(S_180 > 700) = 1 - PP(S_180 <= 700) = 1 - Phi((700 - 180 dot 91 / 6) / sqrt(180 dot 35 / 12)) = \
      = 1 - Phi(2/3 sqrt(21)) approx 0.00113
    $
  ]
]

#line(length: 100%)
#task()[]
#solution()[
  Для $alpha < 1/2$
  Пусть $X_n = (S_n - n dot EE xi_k) / sqrt(n sigma^2) = S_n / sqrt(n sigma^2)$. Тогда по ЦПТ, т.к. $D xi_k = sigma^2 < +infinity$
  $ X_n -->^d cal(N)(0, 1) eq.colon X $
  Тогда
  $ PP(lr(|S_n / n^alpha|) < b) = PP((|S_n|) / sqrt(n sigma^2) < (b n^alpha) / sqrt(n sigma^2) ) $
  Пусть $Y_n = (b n^alpha) / sqrt(n sigma^2)$. Тогда для $alpha < 1/2$
  $ Y_n = b / sqrt(sigma^2) dot n^(alpha - 1/2) --> 0 $
  Возьмeм произвольное $epsilon > 0$. Тогда т.к. $X_n -> 0$, то $X_n < epsilon$ начиная с какого-то $N$. Тогда
  $ overline(lim) PP (|X_n| < Y_n) <= overline(lim) PP(|X_n| < epsilon) = PP(|X| < epsilon) -->_(epsilon --> 0) 0 $
  $ lim PP(lr(|S_n / n^alpha|) < b) <= PP(|X| < epsilon) --> 0 $
  Получается что $lim PP(lr(|S_n / n^alpha|) < b) = 0$ при $alpha < 1/2$

  Для $alpha > 1/2$. Тогда $Y_n --> infinity$ и для произвольного $delta > 0$ начиная с какого-то $N$ имеем $Y_n > delta$. Тогда
  $ {|X_n| < delta} subset {|X_n| < Y_n} \ 
    PP(|X_n| < delta) <= PP(|X_n| < Y_n) \
    overline(lim) PP(|X_n| < delta) <= overline(lim) PP(|X_n| < Y_n) \
    1 <--_(delta -> + infinity) PP(|X| < delta) <= overline(lim) PP(|X_n| < Y_n) = lim PP(lr(|S_n / n^alpha|) < b) \
  $
  Значит $lim PP(lr(|S_n / n^alpha|) < b) = 1$ для $alpha > 1/2$
]

#line(length: 100%)
#task()[]
#solution()[
  Пусть $A_n = sum_k^n xi_k$. Тогда по ЦПТ
  $ (A_n - n dot EE xi_k) / sqrt(n dot DD xi_k) = (A_n - n dot 0) / sqrt(n dot 1) = A_n / sqrt(n) -->^d cal(N)(0, 1) $
  Пусть $B_n = sum_k^n xi_k^2$. Можем найти $EE xi_k^2$ чере $DD xi$:
  $ DD xi_k = EE xi_k^2 - EE^2 xi_k = EE xi_k^2 - 0^2 = EE xi_k^2 = 1 $
  $ EE B_n = sum_k^n EE xi_k^2 = n EE xi_k^2 $
  Тогда по УЗБЧ
  $ B_n / n - EE B_n / n --> 0 #text[п.н.] ==>  B_n / n --> EE B_n / n #text[п.н.] $
  $ EE B_n / n = (n EE xi_k^2) / n = EE xi_k^2 = 1 $
  Отсюда получаем что $B_n / n --> 1 #text[п.н.]$, а т.к. $B_n >= 0$ (и видимо $B_n > 0$), то и $sqrt(n / B_n) --> 1 #text[п.н.]$. По свойствам сходимостей с.в. $1 / sqrt(B_n / n) -->^PP 1$. По теореме Слуцкого:
  $ A_n / sqrt(n) dot sqrt(n) / sqrt(B_n) = (xi_1 + dots + xi_n) / sqrt(xi_1^2 + dots + xi_n^2) -->^d 1 dot cal(N)(0, 1) = cal(N)(0, 1) $
]

#line(length: 100%)
#task()[]
#solution()[
  Пусть $xi_k$ --- количество очков за $k$-тый выстрел.
  $ EE xi_k = 10 dot 0.35 + 9 dot 0.3 + 8 dot 0.2 + 7 dot 0.1 + 6 dot 0.05 = 8.8 $
  $ EE xi_k^2 = 10^2 dot 0.35 + 9^2 dot 0.3 + 8^2 dot 0.2 + 7^2 dot 0.1 + 6^2 dot 0.05 = 78.8 $
  $ DD xi_k = EE xi_k^2 - EE^2 xi_k = 78.8 - 8.8^2 = 1.36 $
  Хотим найти вероятность, сдвинутую на $0.5$ чтобы включить $S_100 = 900$
  $ PP(S_100 >= 900) = PP(S_100 >= 900.5) = 1 - PP(S_100 < 900.5) = 1 - PP(S_100 <= 900) $
  Тогда можем применить ЦПТ
  $ PP(S_100 >= 900) = 1 - PP((S_100 - 100 dot 8.8) / sqrt(100 dot 1.36) <= (900 - 100 dot 8.8) / sqrt(100 dot 1.36))  --> 1 - Phi((900 - 100 dot 8.8) / sqrt(100 dot 1.36)) approx 0.0432 $
]
