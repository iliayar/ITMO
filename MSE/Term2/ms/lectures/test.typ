#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Заметки к контрольной],
  date: [9 апреля],
  number: 0,
  program: "ITMO MSE y2025",
  doc
)

#definition[
  $cal(P)$ --- распределение на прямой. 
  - $X_1, dots, X_n$ --- н.о.р.с.в. с распределением $cal(P)$ --- *выборка*. (до эксперимена)
  - $X_1, dots, X_n$ --- числа --- *выборка*. (после эксперимента)
]

#definition[
  *Выборочное (эмпирическое) распределение* --- дискретное равномерное распределение с атомами в точках выборки
  $ overline(cal(P)_n) = mat(X_1, dots, X_n; 1/n, dots, 1/n) $
]

#definition[
  *Выборочная характеристика*. $Pi$ --- множество всех распределение на прямой. $T : Pi -> overline(RR) = RR union {+infinity}$ --- характреистика. $T(cal(P))$ --- генеральная характеристика, $T(overline(cal(P)_n))$ --- эмпирическая характеристика
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Распределение Бернулли. Принимает значения $0$ и $1$.
  - $DD X = p (1 - p)$
  - $EE X = p$

  Это например индикаторы $bb(1){dots}$.
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Биноминальное распределение. $X_i$ с распределение Бернулли. $S_n = sum X_i ~ "Bin"(n, p)$
  - $EE S_n = n p$
  - $DD S_n = n p q$
  - Функция вероятности 
    $ f_(S_n) (k) equiv PP(S_n = k) = binom(n, k) p^k q^(n - k) $

  Это например сумма индикаторов $sum bb(1){dots}$
]

#definition[
  $z_p$ --- *$p$-квантиль* для $cal(P)$, если $z_p = sup { z : F(z) < p }$. Эмпирические квантили $overline(z_p) = sup {z : overline(F_n)(z) <= p}$
]

#definition[
  $overline(a)_n$ --- (выборочная характеристика) *состоятельная оценка генеральной*  характеристики $a$, если $overline(a)_n ->^PP a$.
]

#remark[
  ЗБЧ. $X_1, dots, X_n$ --- независимые о. р. $EE X_i = a < +infinity$
  $ 1/n sum_(i = 1)^n X_i ->_(n -> +infinity) a #text[п.н.] $
  $ 1/n sum_(i = 1)^n X_i ->^PP_(n -> +infinity) a $
]

#statement[
  - $X_n^((1)) ->^PP z_1 = "const"$
  - $dots$
  - $X_n^((k)) ->^PP z_k = "const"$
  $f$ --- функция $k$ переменных, непрерывная в окрестности $(z_1, dots, z_k)$. $f : RR^n -> RR$. Тогда
  $ f(X_n^((1)), dots, X_n^((k))) ->^PP f(z_1, dots, z_k) $
]

#theorem("Гливенко-Кантелли")[
  $ sup_X |overline(F_n) (x) - F(x)| ->_(n -> +infinity) 0 #text[п.н.] $
]

#statement[
  Если генеральный квантиль $z_p$ такой что $F(z_p) = p$ и $F$ --- непрерывна и строго возрастает в окрестности $z_p$, то $overline(z)_p ->^PP z_p$.
]

#definition[
  Выборочная характеристика $overline(a)_n$ --- *несмещенная оценка* $a$, если $forall n med EE overline(a)_n = a_i$
]
#definition[
  Выборочная характеристика $overline(a)_n$ --- *ассимптотически несмещенная оценка* $a$, если $EE overline(a)_n ->_(n -> +infinity) a_i$
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Равномерное распределение.
  - $EE X = (a + b) / 2$
  - $DD X = (b - a)^2 / 12$
  $ f_X (x) = cases(1 / (b - a)"," quad & x in [a, b], 0"," & x in.not [a, b]) $
  $ F_X (x) equiv PP(X < x) = cases(0"," quad & x < a, (x - a) / (b - a)"," & a <= x < b, 1"," & x >= b) $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Для определения несмещенности считаем матожидание и считаем параметр распределения неизвестным. Полезные штуки
  $ EE X = integral_a^b x f_X (x) d x quad f_X (x) = F'_X (x) $

  Для проверки состоятельности выражаем через определение сходимости по вероятности:
  $ PP(|overline(a)_n - a| > epsilon) -> 0 $
  Либо доказываем для любого $epsilon$, либо приводим контрпример $epsilon = dots$.
]

#remark[
  $X_1, dots, X_n ~ cal(P)_theta$, где $theta in Theta subset RR^d$, где $Theta$ --- пространство параметров
]

#definition[
  Оценка --- любая (измеримая) функция от выборки, на зависящая от значения неизвестного параметра. $hat(theta)$
]


#definition[
  $hat(theta)_n$ --- *несмещенная* оценка параметра $theta$ если $EE hat(theta)_n = theta, forall theta in Theta$
]
#remark[
  Вообще говоря $hat(theta)_n$ это случайная величина которая зависит от параметра $theta$
]

#definition[
  $hat(theta)_n$ *ассимпотически* несмещена, если $EE hat(theta)_n ->_(n -> +infinity) theta, forall theta in Theta$
]

#definition[
  $hat(theta)_n$ --- *состоятельная* если $hat(theta)_n ->^PP_(n -> +infinity), forall theta in Theta$
]

#remark[
  Метод выборочных характеристик (моментов). Есть выборочная характеристика $T: Pi -> overline(R)$ (${cal(P)_theta} -> overline(R)$). $T(cal(P)_theta) = h(theta) ==> theta = h^(-1)(T(cal(P)_theta))$
  $ hat(theta)_n = h^(-1) (T(overline(cal(P))_n)) = hat(theta)_n (X_1, dots, X_n) $

  Семейство уравнений $h(hat(theta)_n) = T(overline(cal(P))_n)$. Хотим узнать:
  1. Сущесвует ли решение и единственно ли оно
  2. Принадлежит ли решение $hat(theta)_n$ пространству $Theta$

  Схема решения:
  1. Выбираем характеристику $T$
  2. Считаем $h(theta) = T(cal(P)_theta)$
  3. Имея выборку $(X_1, dots, X_n)$ считаем выборочную характеристику 
  4. Объявляем что оценка $hat(theta)_n$ является решением системы уравнений $h(hat(theta)_n) = T(overline(cal(P))_n)$
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Экспоненциальное распределение $"Exp"(lambda)$
  - $f_X (x) = lambda e^(- lambda x)$ при $x >= 0$
  - $F_X (x) = 1 - e^(-lambda x)$ при $x >= 0$
  - $EE X = 1 / lambda$
  - $DD X = 1 / lambda^2$
]

#remark[
  Сравнение оценок через среднеквадратическое отклонение
  $ EE (hat(theta)_n - theta)^2 = DD hat(theta)_n + (EE hat(theta) - theta)^2 $
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Распределение Пуассона
  - $p(k) equiv PP(X = k) = (lambda^k) / (k!) e^(-lambda)$
  - $EE X = lambda$
  - $DD X = lambda$
]

#remark("Метод максимального правдоподобия")[
  1. $X_1, dots, X_n ~ cal(P)_theta$ --- дискретное. Т.е. для каждого значения вероятность $p_theta(y_i)$. Можем посчитать вероятность что получим именно эти числа
    $ PP(X_1, dots, X_n) = product p_theta (x_i) = L(theta) $
    где $L$ --- функция правдоподобия
    $ cal(l)(theta) := sum_(i = 1)^n log p_theta (x_i) $
    $ hat(theta)_n = "argmax"_theta L(theta) = "argmax"_theta l(theta) $
    Хотим найти решение $hat(theta)'_n = 0$.

    $ L(theta) = product p_theta (x_i) = theta^(X_1 + dots + X_n) (1 - theta)^(n - X_1 - dots - X_n) = \
      theta^(n overline(X)) (1 - theta)^(n (1 - overline(X))) \
      l(theta) = n overline(X) log theta + n (1 - overline(X)) log (1 - theta) \
      hat(theta)'_n = (n overline(X)) / theta - (n (1 - overline(X))) / (1 - theta) = 0 ==> theta = overline(X)
    $
  2. $cal(P)_theta$ --- абсолютно непрерывное. $p_theta (y)$ --- плотность
    $ L(theta) = product_(i = 1)^n p_theta (x_i) $
]
#theorem[
  При выполнении некоторых условий регулярности для ОМП:
  $ sqrt(n) (hat(theta)_n - theta_0) ->^d cal(N)(0, I^(-1) (theta_0)) $
  Это значит что
  $ PP(sqrt(n) (hat(theta)_n - theta_0) < x) -> Phi_(I^(-1) (theta_0)) (x) $
]

#corollary[
  1. ОМП $hat(theta)_n$ --- состоятельная
  2. ОМП $hat(theta)_n$ --- ассимптотически несмещенная
  3. $DD hat(theta)_n -> 1 / I(theta_0) ==> DD hat(theta)_n = O(1 / n)$
]

#remark[
  Один из вариантов условий регулярности.
  1. Распределение абсолютно непрерывно (сущесвует $p_theta$ --- плотность)
  2. $p_theta (x) > 0$ на множестве не зависящем от $theta$
  3. $I(theta) = EE (partial / (partial theta) log p_theta (x))^2$ --- непрерывен по $theta$, конечен, $> 0$
]

#theorem("Неравенство Рао-Крамера")[
  Пусть $hat(theta)_n$ --- существует $DD hat(theta)_n$, $b_n (theta) = EE (hat(theta)_n - theta)$. Тогда при выполнении условий регулярности
  $ DD hat(theta)_n + b_n^2 (theta_0) = EE (hat(theta)_n - theta)^2 >= (1 + b'_n (theta_0))^2 / (n I(theta_0)) + b_n^2 (theta_0) $
]

#corollary[
  $ DD hat(theta)_n >= (1 + b'_n (theta_0))^2 / (n I (theta_0)) $
  Для несмещенных
  $ DD hat(theta)_n >= 1 / (n I(theta_0)) $
]

#definition[
  $hat(theta)_n$ --- (R-)эффективная если м неравенстве Рао-Крамера имеет место равенство $forall theta_0$. 
  Для несмещенных это значит
  $ DD hat(theta)_n = 1 / (n I(theta_0)) $
]

#definition[
  $hat(theta)_n$ --- ассимптотически (R-)эффективной если в неравенстве Рао-Крамера достигается равенство при $n -> +infinity$.
]

#statement[
  ОМП --- ассимптотически (R-)эффективные
]

#remark[
  Доверительные интервалы. $gamma in (0, 1)$ --- доверительный уровень. $hat(theta)_n^-, hat(theta)_n^+$ --- статистики.
]

#definition[
  1. $(hat(theta)_n^-, hat(theta)_n^+)$ --- доверительный интервал уровня $gamma$, если
    $ PP(hat(theta)_n^- < theta < hat(theta)_n^+) = gamma $
  2. гарантированного уровня $gamma$, если
    $ PP(hat(theta)_n^- < theta < hat(theta)_n^+) >= gamma $
  3. ассимптотического доверительного уровня $gamma$
    $ PP(hat(theta)_n^- < theta < hat(theta)_n^+) ->_(n -> +infinity) gamma $
]

// #remark[
//   $overline(X) plus.minus z_((1 + gamma) / 2) sigma / sqrt(n)$ --- доверительный ин
// ]

#definition[
  Случайная величина $g(X_1, dots, X_n; theta)$ --- центральная статистика для $theta$
  1. Распределение $g(X_1, dots, X_n; theta)$ --- не зависит от $theta$
  2. $G_n$ --- функция распределения центрального распределения --- непрерывна
  3. $forall z_1, z_2 : z_1 < g(X_1, dots, X_n; theta) < z_2$, $exists f_1, f_2 : forall theta:$
    $ f_1(X_1, dots, X_n; z_1, z_2) < theta f_2(X_1, dots, X_n; z_1, z_2) $
]

#remark[
  1. Фиксируем $gamma$
  2. Выбираем $z_1, z_2$: $G_n(z_2) - G_n(z_1) = gamma$
  3. $ gamma =  G_n(z_2) - G_n(z_1) = PP(z_1 < g(X_1, dots, X_n; theta) < z_2) = \
    = PP(f_1(X_1, dots, X_n; z_1, z_2) < theta < f_1(X_1, dots, X_n; z_1, z_2)) $
]

#statement[
  1. $X_1, dots, X_k ~ cal(N)(0, 1)$. Тогда $X_1^2 + dots + X_k^2 ~ chi^2_k = Gamma(k / 2, 1 / 2)$
  2. $X_1, dots, X_n$ --- н.о.р.с.в. $cal(N)(a, sigma^2)$. Тогда $sqrt(n) (overline(X) - a) / sigma ~ cal(N)(0,1)$ и $sqrt(n - 1) (overline(X) - a) / overline(s)_a ~ t_(n - 1)$ --- распределение Стьюдента с $n - 1$ степенью свободы
  3. $X_1, dots, X_n$ --- н.о.р $cal(N)(a, sigma^2)$
    $ sum_(i = 1)^n (X_i - a)^2 / sigma^2 ~ xi^2_n $
    $ sum_(i = 1)^n (X_i - overline(X))^2 / sigma^2 ~ xi^2_(n - 1) $
]

#theorem("ЦПТ")[
  $X_1, dots, X_n$ --- н.о.р $DD X_i = sigma^2 < +infinity$, $EE X_i = a$
  $ sqrt(n) (overline(X) - a) / sigma ->^d cal(N)(0, 1) $
  $ PP(z_1 < sqrt(n) (overline(X) - a) / sigma < z_2) -> Phi(z_2) - Phi(z_1) $
]
#corollary[
  $ sqrt(n) (overline(X) - a) / overline(s)_n ->^d cal(N)(0, 1) $
]

#remark(fill: rgb("#FFD580"), inset: 1em)[
  Нормальное распределение. $cal(N)(a, sigma^2)$
  - $EE X = a$
  - $DD X = sigma^2$
  $ f_X (x) = 1 / (sqrt(2 pi) sigma) e^(-1/2 ((x - a) / sigma)^2) $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Нахождение доверительного интервала для $T_n$. Считаем $EE T_n$, $DD T_n$. По ЦПТ строим
  $ PP_theta (z_(1 - epsilon / 2) <= N(T_n, theta) <= z_(epsilon / 2)) $
  Приводим к виду
  $ PP_theta (L(z_1, T_n) <= theta <= R(z_2, T_n)) $

  #lemma("Слуцкого")[
    1. $xi_1, dots, xi_n -->^d xi_0$ --- сулчайная величина
    2. $eta_1, dots, eta_n -->^PP c$ --- константа
    то $f(xi_n, eta_n) -->^d f(xi_0, c)$ если $f$ непрерывна
  ]
  #example[
    Можем избавлятся от параметра по ЗБЧ. $sqrt(T_n) -> sqrt(theta)$ по ЗБЧ.
  ]
]
