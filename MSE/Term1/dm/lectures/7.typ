#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 7],
  date: [22 октября],
  number: 7,
  doc
)

= Схема Бернулли

#remark()[
  - $Omega = {omega_1, dots, omega_n}$
  - $p_1, dots, p_n : p_i >= 0 quad p_1 + p_2 + dots + p_n = 1$
  $ PP(A) = sum_(omega_i in A) p_i $

  Проверим свойства:
  1. $PP(emptyset) = 0$, $PP(Omega) = 1$, $A subset Omega: PP(A) in [0; 1]$
  2. $PP(A union B) = PP(A) + PP(B) - PP(A inter B)$
    - $omega_i in A and omega_i in.not B$. В левую часть внесет $p_i$ и в правую $p_i$.
    - $omega_i in.not A and omega_i in B$. Аналогично
    - $omega_i in A and omega_i in B$. Внесет вклад в левую часть $p_i$. В правую часть $2 p_i - p_i = p_i$
]

#remark()[
  - $Omega = { omega : 9x)1, x_2, dots, x_n) }, x_i in {0, 1}$
  - $p in [0; 1]: PP({omega}) = p^(sum x_i) dot (1 - p)^(sum x_i)$

  "0" --- решка, неудача. "1" --- орел, удача. Тогда $S_n = sum x_i$ --- количество успехов в схеме Бурнулли.
]

#remark()[
  $PP(S_n = k) = binom(n, k) p^k (1 - p)^(n - k)$
]

#remark()[
  $ sum^n_(k = 0) PP(S_n = k) = sum^n_(k = 0) binom(n, k) p^k (1 - p)^(n - k) = (1 + (1 - p))^n = 1 $
]

= Предельные теоремы

#theorem("Пуассона")[
  $n p_n = lambda$, тогда
  $ PP(S_n = k) -->_(n -> + infinity) (lambda ^k dot e^(- lambda)) / k! $
]
#proof()[
  $ PP(S_n = k) = binom(n, k) p_n^k (1 - p_n)^(n - k) = (n (n - 1)(n-  2) dots (n - k + 1)) / k! dot lambda^k / n^k dot (1 - lambda /n)^n dot (1 - lambda /n)^(-k) = \
    = lambda^k / k! dot n / n dot underbrace((n - 1) / n, -> 1) dot underbrace((n - 2) / n, -> 1) dots (n - k + 1) / n dot underbrace((1 - lambda / n)^n, -> e^(- lambda)) dot underbrace((1 - lambda /n)^(-k), -> 1) --> (lambda^k dot e^(- lambda)) / k!
  $
]


#remark()[
  Теорема верна и при $n p_n --> lambda$.
]
#remark()[
  В практическом приенении имеет смылсл только при больших $n$ и $k <= sqrt(n)$
]

#example()[
  Рулетка. Элементарные исходы $0, dots, 36$. Всегда ставим на $7$. $p = 1 / 37, 1-p = 36 / 37$.
  $ PP(S_111 = 2) = binom(111, 2) approx 0.225044 \
    PP(S_111 = 2) approx (3^2 e^(-3)) / 2! = 9 / 2 dot e^(-3) approx 0.22404
  $
  $lambda = 111 dot 1/37 = 3$
]

#theorem("Муавра-Лапласа")[
  $p in (0; 1)$ --- $"const"$, $1 = 1 - p$, $x_k = (k = n p) / sqrt(n p q)$. Если при $n -> infinity$ $k$ меняется так, что $|x_k| <= T$. Тогда $PP(S_n = k) ~ 1 / sqrt(2 pi n p q) dot 3^(-x^2 / 2)$
]

#remark()[
  Получаем хорошее приближение при $k$ близких к $n p$.
]
#example()[
  Ставим на красное $p = 18 / 37, q = 19 / 37$.
  $ PP(S_222 = 111) = binom(222, 111) (18 / 37)^111 dot (19 / 37)^111 approx 0.04932 \
    x = (111 - 108) / sqrt((108 dot 19) / 37) quad PP(S_222 = 111) = 1 / sqrt(2 pi (108 dot 19) / 37) e^(- 3^2 / (2 dot (108 dot 19) / 37)) approx 0.04935
  $
]

#theorem("Интегральная теорема Муавра-Лапласа")[
  $ PP(a <= (S_n - n p) / sqrt(n p q) <= b) -->_(n -> + infinity) 1 / sqrt(2 pi) integral_a^b e^(-x^2 / 2) d x $
]
#remark()[
  $ 1 / sqrt(2 pi) integral_(- infinity)^t e^(- x ^2 / 2) d x = Phi(t) $
  $Phi(-t) = 1 - Phi(t)$
]
#remark()[
  $ PP(a <= S_n <= b) = PP((a - n p) / sqrt(n p q) <= (S_n - n p) / sqrt(n p q) <= (b - n p) / sqrt(n p q)) approx Phi((b - n p) / sqrt(n p q)) - Phi((a - n p) / sqrt(n p q))
  $
]
#remark()[
  Если вычтем малое число из $b$, то потеряем целый 1 случай, но в контексте $Phi$ значение почти не поменяется. В качестве $a$ и $b$ подставляем $ZZ + 1 / 2$.
]

#example()[
  Задача о гардеробе. В театре с 1600 мест, есть два гардероба, в который равновероятно приходят люди. Сколько мест надо выделить в гардеробе чтобы он не часто переполнялся (что гардероб не переполнится с вероятностью $29 / 30$).

  Размер гардероба $c$.
  $ PP(1600 - c <= S_1600 <= c) = 29/30 $
  $ PP((800 - c) / 20 <= (S_1600 - 800) / 20 <= (c - 800) / 20) approx 1 / sqrt(2 pi) integral^((c - 800) / 2)_((800 - c) / 20) e^(-x^2 / 2) d x = 29 / 30 = $
  $ = Phi((c - 800) / 20) - Phi((800 - c)/ 20) = 2 Phi((c - 800) / 20) - 1 >= 29 / 30 $
  $c = 843$
]
