#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Заметки к контрольной],
  date: [9 апреля],
  number: 0,
  program: "ITMO MSE y2025",
  doc
)

#let practice-color = rgb("#87CEFA")

#definition[
  $cal(P)$ --- распределение на прямой. 
  - $X_1, dots, X_n$ --- н.о.р.с.в. с распределением $cal(P)$ --- *выборка*. (до эксперимента) (на генеральном уровне)
  - $X_1, dots, X_n$ --- числа --- *выборка*. (после эксперимента) (на выборочном уровне)
]

#definition[
  *Выборочное (эмпирическое) распределение* --- дискретное равномерное распределение с атомами в точках выборки
  $ overline(cal(P))_n = mat(X_1, dots, X_n; 1/n, dots, 1/n) $
]

#definition[
  *Выборочная характеристика*. $Pi$ --- множество всех распределение на прямой. $T : Pi -> overline(RR) = RR union {+infinity}$ --- характеристика. $T(cal(P))$ --- генеральная характеристика, $T(overline(cal(P))_n)$ --- эмпирическая характеристика
]

#example[
  Характеристики:
  - Математическое ожидание
    $ m_1 = T (cal(P)) = integral_RR z cal(P)(d z) $
    $ overline(X) = overline(m_1) = T(overline(cal(P))_n) = integral_RR z overline(cal(P))_n (d z) = sum_(i = 1)^n X_i 1 / n = 1/n sum_(i = 1)^n X_i $
  - Дисперсия
    $ sigma^2 = T(cal(P)) = integral_RR (z - m)^2 cal(P)(d z) = integral_RR z^2 cal(P)(d z) - m_1^2 $
    $ overline(s)_n^2 = T(overline(cal(P))_n) = 1/n sum_(i = 1)^n (X_i - overline(X))^2 $
  - Стандартное отклонение $sigma = sqrt(sigma^2)$. $overline(s)_n = sqrt(overline(s)_n^2)$
  - Момента
    $ m_k = integral_RR z^k cal(P)(d z) $
    $ overline(m)_k = 1/n sum_(i = 1)^n X_i^k $
  - Центральный момент
    $ m^((0))_k = integral_RR (z - m_1)^k cal(P)(d z) $
    $ overline(m)^((0))_k = 1/n sum_(i = 1) (X_i - overline(X))^k $

    $ sigma^2 = m_2 - m_1^2 quad overline(s)_n^2 = overline(m)_2 - overline(m)_1^2 $
  - Ковариация. $(X_i, Y_i)$
    $ "cov"(X, Y) = integral_RR (u - m_X) (v - m_Y) cal(P)(d u d v) $
    $ overline("cov")(X, Y) = 1/n sum_(i = 1)^n (X_i - overline(X))(Y_i - overline(Y)) $
  - Корреляция
    $ r(X, Y) = "cov"(X, Y) / (sigma_X sigma_Y) $
  - Функция распределения в точке
    $ F(z) = T(cal(P)) = PP(X_i < z) = cal(P)((-infinity, z)) $
    $ overline(F)_n (z) = overline(cal(P))_n ((-infinity, z)) $
]

#definition[
  Эмпирическая функция распределения
    $ overline(F)_n (z) = overline(cal(P))_n ((-infinity, z)) = (\#{X_i < z}) / n $
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
  $z_p$ --- квантиль уровня $p$, где $0 < p < 1$, если $F(z_p) = p$.
]

#definition[
  $z_p$ --- *$p$-квантиль* для $cal(P)$, если $z_p = sup { z : F(z) < p }$. Эмпирические квантили $overline(z_p) = sup {z : overline(F_n)(z) <= p}$
]

#remark[
  Выборочная медиана:
  - $n = 2k + 1$ --- $overline(z)_(1 / 2) = X_([k + 1])$
  - $n = 2k$
    - $overline(z)_(1 / 2) = X_([k + 1])$
    - $overline(z)_(1 / 2) = 1/2 (X_([k]) + X_([k + 1]))$
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

#example[
  Хотим показать что $overline(s)_n^2 ->^PP sigma^2$. $overline(s)_n^2 = overline(m)_2 - overline(m)_1^2$. И при этом $overline(m)_2 -> m_2$ и $overline(m)_1 -> m_1$. Тогда если возьмем $f(x, y) = x - y^2$ то можем применить утверждение выше: 
  $ f(overline(m)_2, overline(m)_1^2) = overline(m)_2 - overline(m)_1^2 -> m_2 - m_1^2 = sigma^2 $
]

#example[
  $overline(F)_n (x) ->^PP F(x)$?
  Введем $Y_i := bb(1)_{X_i < x}$
  $ PP(Y_i = 1) = PP(X_i < X) = F(x) $
  $ overline(F)_n (x) = (\#{X_i < X}) / n = 1 / n sum_(i = 1)^n Y_i = overline(Y) $
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

#remark(fill: practice-color, inset: 1em)[
  1. $forall theta thick EE_theta T_n = theta$ --- несмещенность
  2. $forall theta thick EE_theta T_n ->_(n -> +infinity) theta$ --- ассимптотически несмещенная
  3. $T_n ->^PP theta$ --- состоятельная оценка

  #remark[
    Если оценка несмещенная и $DD X_i -> 0$, то оценка состоятельная
  ]
  #remark[
    $ DD (X + Y) <= (sqrt(DD X) + sqrt(DD Y))^2 $
  ]
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
  $hat(theta)_n$ --- *состоятельная* если $hat(theta)_n ->^PP_(n -> +infinity) theta, forall theta in Theta$
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
    $ sum_(i = 1)^n (X_i - a)^2 / sigma^2 ~ chi^2_n $
    $ sum_(i = 1)^n (X_i - overline(X))^2 / sigma^2 ~ chi^2_(n - 1) $
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

#remark([Дельта-метод])[
   В условиях ЦПТ: $X_1, dots, X_n$ --- н.о.р. $EE X_i = mu$, $DD X_i = sigma^2$.
   $ sqrt(n) (overline(X)_n - mu) ->^d_(n -> +infinity) sigma Z ~ cal(N)(0, sigma^2) $
   где $Z ~ cal(N)(0, 1)$.
   Рассмотрим $g(t) = a t + b$, $Y_n = g(overline(X)_n)$
   $ EE Y_n = a mu + b = g(mu) quad DD Y_n = a^2 sigma^2 $.
   Рассмотрим
   $ sqrt(n) (g(overline(X)_n) - g(mu)) = sqrt(n) (a overline(X)_n + b - a mu - b) = sqrt(n) a (overline(X)_n - mu) $
   Тогда
   $ sqrt(n) (g(overline(X)_n) - g(mu)) ->^d a sigma Z ~ cal(N)(0, a^2 sigma^2) $
   Разложим по Тейлору
   $ g(t) = g(mu) + g'(mu)(t - mu) + o(t - mu), quad t -> mu $
   $ g(overline(X)_n) - g(mu) = g'(mu)(overline(X)_n - mu) + o(dots) $
]

#theorem([Дельта-метод])[
  $X_n$ --- последовательность с.в., $X$ --- с.в. Пусть для $b > 0 med exists a:$
  $ n^b (X_n - a) ->^d X $
  Пусть $exists g'(a) != 0$, тогда
  $ n^b (g(X_n) - g(a)) ->^d g'(a) X $
]
#corollary([Дельта-метод + ЦПТ])[
  $ sqrt(n) (overline(X)_n - mu) ->^d cal(N)(0, sigma^2) ==> \
    ==> sqrt(n) (g(overline(X)_n) - g(mu)) ->^d cal(N)(0, sigma^2 g'(mu)^2)
  $
  при $g'(mu) != 0$
]

#example[
  $overline(X)_n^2 -> ?$. $mu != 0 ==> g'(mu) != 0$
  $ g(t) = t^2 quad g'(t) = 2t $
  Тогда
  $ sqrt(n) (overline(X)_n^2 - mu^2) ->^d cal(N)(0, 4 mu^2 sigma^2) $
]
#remark[
  Пуст $g'(mu) = 0$, тогда раскалдываем до второй производной
  $ g(X_n) - g(mu) = 1 / (2!) g''(mu)(X_n - mu)^2 + o(dots) $
  $ n^(2 b) (g(X_n) - g(mu)) = 1 / (2!) g''(mu) (n^b (X_n - mu))^2 $
]
#example[
  $ g(t) = t^2 quad g'(t) = 2t quad g''(t) = 2 $
  При $mu = 0$
  $ n(overline(X)_n)^2 ->^d sigma^2 chi^2_1 $
]

#example[
  $X_1, dots, X_n ~ "Exp"(lambda)$. $p(x) = lambda e^(- lambda x), x > 0$
  Оценка по методу моментов:
  $ EE X_i = 1 / lambda ==> lambda_n = 1 / overline(X)_n $
  По ЦПТ:
  $ sqrt(n) (overline(X)_n - 1 / lambda) ->^d cal(N)(0, 1 / lambda^2) $

  $g(t) = 1/t$, $g'(t) = -1/t^2$
  $ sqrt(n) (g(overline(X)_n) - g(1 / lambda)) = sqrt(n) (1 / overline(X)_n - lambda) ->^d g'(1 / lambda) dot 1/lambda Z = -lambda dot Z ~ cal(N)(0, lambda^2) $
]

#remark[
  Преобразования, стабилизирующие дисперсию.
  #example[
    $X_1, dots, X_n ~ cal(N)(0, sigma^2)$. $Y_i := X_i^2$. $EE Y_i = EE X_i^2 = sigma^2$, $DD Y_i = DD X_i^2 = 2 sigma^4$.
    По ЦПТ:
    $ sqrt(n) (1 / n sum_(i = 1)^n X_i^2 - sigma^2) ->^d cal(N)(0, 2 sigma^4) $
    $ sqrt(n) (1/n sum_(i = 1)^n X_i^2 - sigma^2) / (sqrt(2) sigma^2) ->^d cal(N)(0, 1) $
  ]
]

= Проверка статистических гипотез

#remark[
  $X_1, dots, X_n$ --- выборка с некоторым распределением $P_0 in cal(P)$. $H_0$ --- предикат на $cal(P)$ ($H_0 : cal(P) -> {T, F}$). Задача: по выборке $X_1, dots, X_n$ проверить $H_0 (P_0)$. Можно считать что $H_0 : cal(P)_0 subset cal(P)$.
]

#example[
  $cal(P) = {P_theta | theta in Theta}$. Тогда $cal(P)_0 = {P_theta | theta in Theta_0}$. $exists theta' : P_0 = P_(theta')$. Правда ли что $theta' in Theta_0$.
]


#remark[
  Задача: построить *критерий* $phi(X_1, dots, X_n)$: $phi(X_1, dots, X_n) = cases(0"," H_0, 1"," not H_0 = H_1)$.
]

#definition[
  *Критическое множество* $S = {(X_1, dots, X_n) : phi(X_1, dots, X_n) = 1}$. *Доверительное множество* $D = {(X_1, dots, X_n) : phi(X_1, dots, X_n) = 0}$.
]

#remark[
  - Ошибка I рода: $phi$ отвергает гипотезу $H_0$ когда она верна. $phi(X_1, dots, X_n) = 1$, но $X_1, dots, X_n ~ P_0 in cal(P)_0$.
  - Ошибка II рода: $phi$ принимает $H_0$ когда она неверна. $phi(X_1, dots, X_n) = 0$, но $X_1, dots, X_n ~ P_0 in.not cal(P)_0$.
  - $alpha_I = P((X_1, dots, X_n) in S | P_0 in cal(P)_0} = PP(H_1 | H_0)$
  - $alpha_(I I) = P((X_1, dots, X_n) in D | P_0 in.not cal(P)_0) = PP(H_0 | H_1)$
]

#example[
  $cal(P) = {cal(N)(a_1, sigma^2), cal(N){a_2, sigma^2)}$. $H_0 : a = a_1$, $H_1 : a = a_2$. Пусть $z = sqrt(n) (overline(X) - a_1) / sigma$. Если верна $H_0$, то $z ~_(H_0) cal(N)(0, 1)$. Пусть $phi(X_1, dots, X_n) = cases(0"," |z| < 1.96, 1","#[иначе])$
  $ alpha_I = PP(H_1 | H_0) = PP(phi(X_1, dots, X_n) = 1 | a = a_1) \
    = PP(|z| >= 1.96 | z ~ cal(N)(0, 1)) = Phi(-1.96) + (1 - Phi(1.96)) = 0.05 $
  $ z = sqrt(n) (overline(X) - a_1) / sigma = sqrt(n) (overline(X) - a_2) / sigma + sqrt(n) (a_2 - a_1) / sigma $
  Если верна $H_1$, тогда:
  $ z ~_(H_1) cal(N) (sqrt(n) (a_2 - a_1) / sigma, 1) =: Phi_1 $
  $ alpha_(I I) = PP(|z| < 1.96), z ~ Phi_1) = Phi_1(1.96) - Phi_1(-1.96) $
  $ Phi_1(z) = Phi(z - sqrt(n) (a_2 - a_1) / sigma) $
]

#remark[
  Общая схема построения критерия.
  1. Выбираем статистику критерия $t: (X_1, dots, X_n) -> RR$
  2. Известно распределение $t$ при верной $H_0$ ($cal(L)(t | H_0)$)
  3. $alpha$ --- уровень значимости
  4. Выбор критической области $S_alpha$:
    $ PP(t in S_alpha | H_0) = alpha $
  5. Строим критерий $phi(X_1, dots, X_n) = cases(H_0"," t in.not S_alpha, H_1"," t in S_alpha)$.

  Итого: $alpha_I = alpha$.
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Ошибка первого рода $EE_(H_0) phi(X)$, второго рода $1 - EE_(H_1) phi(X)$, мощность $EE_(H_1) phi(X)$.
  #example[
    $ phi(X) = bb(1) { X_((n)) >= 3 } $
    $ EE_(H_0) bb(1) {X_((n)) >= 3} = PP_(H_0) (X_((n)) >= 3) $
  ]
]

#remark[
  Доверительные интервалы vs проверка гипотез. $X_1, dots, X_n ~ cal(P)_(theta_0)$
  $ PP ((hat(theta)_n^-, hat(theta)_n^+) in.rev theta_0) = gamma $
  $H_0 : theta = theta^*$. Схема построения
  1. Строим доверительный интервал $(hat(theta)_n^-, hat(theta)_n^+)$
  2. Проверяем $theta^* in (hat(theta)_n^-, hat(theta)_n^+)$.
  $ alpha_I = PP (theta^* in (hat(theta)_n^-, hat(theta)_n^+) | theta^* = theta_0) = 1 - gamma $
]

#remark([p-value])[
  Пусть для $alpha > alpha' : S_(alpha') subset.eq S_alpha$. Можем взять ${S_alpha}_(alpha in (0, 1))$. Тогда можем ввести p-value:
  $ p(X_1, dots, X_n) = inf_alpha { t(X_1, dots, X_n) in S_alpha } $
  Это минимальный уровень значимости который начинает отвергать гипотезу *для конкретной* выборки.
]

#remark[
  Проверка гипотез через p-value:
  1. Фиксируем пороговый уровень $p^*$ ($0.05$)
  2. $X_1, dots, X_n |-> p(X_1, dots, X_n)$
  3. $H_0$ --- отвергаем, если $p(X_1, dots, X_n) < p^*$ ($<==> t(X_1, dots, X_n) in S_alpha : alpha >= p^*$).
]

#theorem([о p-value])[
  $ PP(p(X_1, dots, X_n) < x | H_0) = x $
  тогда при верной $H_0$ p-value имеет равномерное распределение на $[0, 1]$.
]

#remark([Одновыборочный t-критерий])[
  $X_1, dots, X_n ~ cal(N)(a, sigma^2)$ ($sigma^2$ неизвестна)
  $ H_0 : a = a_0 quad H_1 : a != a_0 $
  В качестве статистики $t = sqrt(n - 1) (overline(X) - a_0) / overline(s)_n ~_(H_0) t_(n - 1)$. Тогда $S_alpha = (- infinity, z_(alpha / 2)) union (z_(1 - alpha / 2), +infinity)$.
]
#remark([Критерий Фишера])[
  $X_1, dots, X_n ~ cal(N)(a, sigma^2)$.
  $ H_0 : sigma^2 = sigma^2_0 quad H_1 : sigma^2 != sigma^2_0 $
  $ (sum_(i = 1)^n (X_i - overline(X))^2) / sigma^2_0 ~_(H_0) chi^2_(n - 1) $
  В качестве статистики $t = (n overline(s)_n^2) / (sigma^2_0)$. $S_alpha = (0, z_(alpha / 2)) union (z_(1 - alpha/2), +infinity)$
  где $overline(s)_n$ --- исправленное стандартное отклонение
]

#remark[
  Точный критерий $alpha_I = alpha$. Ассимптотический критерий $alpha_I ->_(n -> +infinity) alpha$.
]

#remark([z-критерий])[
  $X_1, dots, X_n$ --- н.о.р.с.в. $EE X_i = a$, $DD X_i = sigma^2 < + infinity$.
  $ H_0 : a = a_0 quad H_1 : a != a_0 $
  $ z = sqrt(n) (overline(X) - a_0) / overline(s)_n ->^d_(H_0) cal(N)(0, 1) $
  $S_alpha : (-infinity, z_(alpha / 2)) union (z_(1 - alpha/2), +infinity)$
]

#example([Типичная ошибка])[
  $X_1, dots, X_n$ --- н.о.р.с.в $EE X_i = a$, $DD X_i = sigma^2$.
  $ H_0 : a = a_0 $
  $ z = sqrt(n) (overline(X) - a_0) / overline(s)_n $
  z-критерий предписивыет использовать критическую область с квантилями из нормального распределения $S_alpha^cal(N) : (-infinity, z_(alpha / 2)) union (z_(1 - alpha / 2), +infinity)$. *Ошибка*: давайте возьмем квантили Стьюдента.
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  #lemma([Фишера])[
    $X_1, dots, X_n ~ cal(N)(theta, sigma^2)$ --- н.о.р.с.в.
    $ overline(X) = (sum X_i) / n quad s_n^2 = 1 / n sum (X_i - overline(X))^2 quad s^2 = n / (n - 1) s_n^2 $
    1. $sqrt(n) (overline(X) - theta) / sqrt(sigma^2) ~ cal(N)(0, 1)$
    2. $overline(X)$ и $s^2$ независимы
    3. $((n - 1) s^2) / sigma^2 = (n s_n^2) / sigma^2 ~ chi^2_(n - 1)$
    4. $sqrt(n - 1) (overline(X) - theta) / sqrt(s_n^2) = sqrt(n) (overline(X) - theta) / sqrt(s^2) ~ T_(n - 1)$
  ]
  #table(
    stroke: none,
    columns: 3,
    $H_0$, table.vline(), $H_1$, table.vline(), [Область принятия $H_0$],
    table.hline(),
    table.cell(rowspan: 3)[$sigma^2$ --- известно \ $theta = m_0$], [$theta != m_0$], [$ sqrt(n) / sqrt(sigma^2) |overline(X) - m_0| <= z_(1 - alpha /2) $],
    [$theta > m_0$], [$ sqrt(n) / sqrt(sigma^2) (overline(X) - m_0) <= z_(1 - alpha) $],
    [$theta < m_0$], [$ sqrt(n) / sqrt(sigma^2) (overline(X) - m_0) >= z_(alpha) = -z_(1 - alpha) $],
    table.hline(),
    table.cell(rowspan: 3)[$sigma^2$ --- неизвестно \ $theta = m_0$], [$theta != m_0$], [$ sqrt(n) / sqrt(s^2) |overline(X) - m_0| <= t_(1 - alpha/2) (n - 1) $],
    [$theta > m_0$], [$ sqrt(n) / sqrt(s^2) (overline(X) - m_0) <= t_(1 - alpha) (n - 1) $],
    [$theta < m_0$], [$ sqrt(n) / sqrt(s^2) (overline(X) - m_0) >= -t_(1 - alpha) (n - 1) $],
    table.hline(),
    table.cell(rowspan: 3)[$sigma = sigma_0$], [$sigma != sigma_0$], [$ chi_(alpha / 2)^2 (n - 1) <= (n - 1) s^2 / sigma_0^2 <= chi_(1 - alpha / 2)^2 (n - 1) $],
    [$sigma > sigma_0$], [$ (n - 1) s^2 / sigma_0^2 <= chi_(1 - alpha)^2 (n - 1) $],
    [$sigma < sigma_0$], [$ (n - 1) s^2 / sigma_0^2 >= chi_(alpha)^2 (n - 1) $],
  )
]

== Двухвыборочные критерии

#remark[
  $X_1^((1)), dots, X_n^((1)) ~ cal(P)_1$, $X_1^((2)), dots, X_m^((2)) ~ cal(P)_2$. $H_0$ : что-то относительно $(cal(P)_1, cal(P)_2)$.
]

#remark([Двухвыборочный t-критерий])[
  - $X_1^((1)), dots, X_n^((1)) ~ cal(N)(a_1, sigma^2)$
  - $X_1^((2)), dots, X_n^((2)) ~ cal(N)(a_2, sigma^2)$
  - Дисперсии равны и известны
  - Обе выборки независимы в совокупности
  $ H_0 : a_1 = a_2 quad H_1 . a_1 != a_2 $
  $ T = (overline(X)_1 - overline(X)_2) / (sigma sqrt(1 / m + 1 / n)) ~_(H_0) cal(N)(0, 1) $
]

#remark[
  $sigma^2$ одинаковы но неизвестны.
  $ T = (overline(X)_1 - overline(X)_2) / (sqrt(1 / n + 1 / m) s_(n, m)^(1, 2)) ~_(H_0) t_(m + n - 2) $
  где $s_(n,m)^(1, 2)$ --- несмещенная оценка стандартного отклонения, посчитанная по комбинированный выборки
  $ s_(n, m)^(1, 2) = (n overline(s)_n^2 + m overline(s)_m^2) / (m + n - 2) $
]

#remark([Welch t-test])[
  $sigma_1^2 != sigma_2^2$ и неизвестны.
  $ T = (overline(X)_1 - overline(X)_2) / sqrt(overline(s)_n^2 / n + overline(s)_m^2 / m) [~ dots] ->^d_(n -> +infinity \ m ->+infinity) cal(N)(0, 1) $
]

#remark[
  - $X_1^((1)), dots, X_n^((1)) ~ B(p_1)$
  - $X_1^((2)), dots, X_n^((2)) ~ B(p_2)$
  $ H_0 : p_1 = p_2 quad H_1 : p_1 != p_2 $
  $ z = overline(X)_1 - overline(X)_2 / (sqrt(1 / m + 1 / n) sqrt(tilde(p) (1 - tilde(p)))) ->^d_(H_0) cal(N)(0, 1) $
  где $tilde(p) = (n overline(X)_1 + m overline(X)_2) / (n + m)$
]

#remark([Двухвыборочный z-критерий])[
  - $X_1^((1)), dots, X_n^((1))$, $DD X_i^((1)) < +infinity$, $EE X_i^((1)) = a_1$
  - $X_1^((2)), dots, X_n^((2))$, $DD X_i^((2)) < +infinity$, $EE X_i^((2)) = a_2$
  $ H_0 : a_1 = a_2 quad H_1 : a_1 != a_2 $
  $ z = (overline(X)_1 - overline(X)_2) / sqrt(overline(s)_n^2 / n + overline(s)_m^2 / m) ->^d_(H_0) cal(N)(0, 1) $
]


#remark(fill: rgb("#87CEFA"), inset: 1em)[
  $X_1, dots, X_2 ~ cal(N)(a_1, sigma^2)$, $Y_1, dots, Y_m ~ cal(N)(a_2, sigma^2)$
  - Дисперсии известны и равны.
    $ overline(X) ~ cal(N)(a_1, sigma^2 / n) quad overline(Y) ~ cal(N)(a_2, sigma^2 / m) $
    $ overline(X) - overline(Y) ~ cal(N)(a_1 - a_2, sigma^2 (1 / n + 1 / m)) $
    $ T := (overline(X) - overline(Y)) / (sigma sqrt(1/n + 1/m)) ~ cal(N)(a_1 - a_2, 1) $
    - $H_0 : a_1 = a_2$, $H_1 : a_1 != a_2$. Область принятия $H_0$: $z_(alpha / 2) <= T <= z_(1 - alpha / 2)$
    - $H_1 : a_1 < a_2$: $z_(alpha) <= T$
    - $H_1 : a_2 > a_2$: $T <= z_(1 - alpha)$
    Где $z$ --- квантили $cal(N)(0, 1)$

  - Если $sigma$ неизвестно:
    $ ((n - 1) s_1^2) / sigma^2 ~ chi^2_(n - 1) quad ((m - 1) s_2^2) / sigma^2 ~ chi^2_(m - 1) $
    $ ((n - 1) s_1^2 + (m - 1) s_2^2) / sigma^2 ~ chi^2_(n + m - 2) $
    $ (cal(N)(0, 1)) / sqrt(chi^2_n / n) ~ T_n $
    $ T = (overline(X) - overline(Y)) / sqrt(((n - 1) s_1^2 + (m - 1) s_2^2) / (n + m) dot (1 / n + 1 / m)) $
    - $H_0 : a_1 = a_2$. $z_(alpha / 2) <= T <= z_(1 - alpha / 2)$
    - $H_1 : a_1 < a_2$: $z_(alpha) <= T$
    - $H_1 : a_2 > a_2$: $T <= z_(1 - alpha)$
    Где $z$ --- квантили $T(n + m - 2)$.

  - Знаем $sigma_1 != sigma_2$
    $ overline(X) - overline(Y) ~ cal(N)(a_1 - a_2, sigma_1^2 / n + sigma_2^2 / m) $
    $ (overline(X) - overline(Y)) / sqrt(sigma_1^2 / n + sigma_2^2 / m) ~ cal(N)(a_1 - a_2, 1) $

  - Если не знаем дисперсии и они не равны
    $ (overline(X) - overline(Y)) / sqrt(s_1^2 / n + s_2^2 / m) ~ T_mu quad mu approx (s_1^2 / n + s_2^2 / m)^2 / ((s_1^2 / n)^2 / (n - 1) + (s_2^2 / m)^2 / (m - 1)) $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  $F$ --- распределение Фишера. $X ~ chi^2_n$, $Y ~ chi^2_m$.
  $ F(n, m) = (X / n) / (Y / m) $
  $ H_0 : sigma_1^2 = sigma_2^2 quad H_1 : sigma_1^2 != sigma_2^2 $
  $ ((n - 1) s_1^2) / sigma_1^2 ~ chi^2_(n - 1) quad ((m - 1) s_2^2) / sigma_2^2 ~ chi^2_(m - 1) $
  Рассмотрим:
  $ (s_1^2 / sigma_1^2) / (s_2^2 / sigma_2^2) ~ F(n - 1, m - 1) $
  $ T = s_1^2 / s_2^2 $
  Область принятия $H_0$: $z_(alpha / 2) <= T <= z_(1 - alpha / 2)$, где $z$ --- квантили $F(n - 1, m - 1)$
]

#remark([Критерий согласия])[
  1. Хи-квадрат
    - $X_1, dots, X_n$ --- выборка, $X_i$ --- дискретная. $x_j$ --- исходы $j = 1 dots m$. $PP(X = x_j) = p_j$, $sum p_j = 1$. Дискретное распределение целиком определяется $(x_j, p_(overline(c))), j = 1 dots m$.
    $ H_0 : #text[все] p_j = PP(X = x_j) quad H_1 : exists j : p_j != PP(X = x_j) $
    Есть набор $O_j = \#{X_i = x_j}, j = 1 dots m$ --- частоты (сколько раз встретился исход $j$). Если верна $H_0$ то $x_j$ встретится $EE_j = n dot p_j$ раз ($H_0 : O_j / n ~ B(p_j)$).

    $ XX^2 = sum_(j = 1)^m (O_j - EE_j)^2 / EE_j = sum_(j = 1)^m (O_j - n p_j)^2 / (n p_j) ->^d_(H_0) chi^2_(m - 1) $
    Это норм если $n p_j > 5$.
]
#remark[
  Если $n p_j < 5$. Можем сгруппировать некоторые вероятности.
]

#remark[
  Превращение непрервыного распределения в дискретное. $(-infinity, +infinity) = union.big.sq_(i = 1)^m (a_i, b_i)$
  $ p_i = PP(X in (a_i, b_i)) = integral_(a_i)^(b_i) p(x) d x quad O_i = \#{X_j in (a_i, b_i)} $

  Будем разбивать чтобы все $p_i$ были равны и чтобы $n p_i > 5$, т.е. $n / m > 5$.
]

#remark[
  Хотим проверить сложную гипотезу. $p_i = p_i (theta)$
  $ XX^2 = XX^2 (theta) = sum_(i = 1)^m (O_i - n p_i (theta))^2 / (n p_i (theta)) $
  $ H_0 : #text[все $p_i (theta_0) = PP(X = x_j)$ для некоторой $theta_0$] $
  $hat(theta)_n$ --- оценка параметра
  $ XX^2 (hat(theta)_n) = sum_(i = 1)^m (O_i -n p_i (hat(theta)_n))^2 / (n p_i (hat(theta)_n)) $
  1. $tilde(theta)_n = "argmax" XX^2 (theta)$
    $ XX^2 ( tilde(theta)_n) ->^d_(H_0)chi^2_(m - 1 - p) $
    где $p = dim Theta$
  2. $hat(theta)_n$ --- ОМП
    $ XX^2 (hat(theta)_n) ->^d_(H_0)chi^2_nu $
    где $m - 1 - p <= nu <= m$
]

#remark([Хи-квадрат и независимость])[
  $(X_i, Y_i)$ --- дискретное
  $ p_(i j) = PP(X = x_i, Y = y_j) $
  $X,Y$ --- независимые $<==> PP(X = x_i) dot PP(Y = y_i)$. $O_(i, j) = \#{X = x_i, y = y_j}$. Таблица $2 times 2$.
  $ EE O_i = n dot p_(i j) = n dot p_i dot p_j' $
  $ hat(p)_1 = (O_(1 1) + O_(1 2)) / n $
  $ H_0 : #text[$X$ и $Y$ независимы $<==>$ все $p_(i j) = p_i dot p_j$] $ 
  $ EE_(i j) = sum_(k = 1)^m O_(i k) dot sum_(k = 1)^m undershell(O_(k j))_(n hat(p)_i dot n hat(p)_j') $
  $ XX^2 = sum_(i = 1)^(m_1) sum_(j = 1)^(m_2) (O_(i j) - EE_(i j)) / EE_(i j) ->^d_(H_0) chi^2_((m_1 - 1) (m_2 - 1)) $
]

#remark([Критерий согласия и абсолютно непрервыные распределения])[
  $X_1, dots, X_n ~ G(x)$ --- абсолютно непрерыное.
  $ H_0 : G(x) = F(x) quad H_1 : G(x) != F(x) $ 
  1. Критерий Колмогорова-Смирнова
    $ D_n = sqrt(n) sup_x (overline(F)_n (x) - F(x)) ->_(H_0) K$
    где $K$ не зависит от $G$ (абсолютно непрерывное)
    $ P(K < x) = sum_(k = -infinity)^(+infinity) (-1)^k e^(-2k^2 x^2) quad x > 0 $
    $ PP(D_n < x) ->_(H_0) PP(K < x) quad forall x $
  2. Критерий Крамера-Смирнова-фон Мизеса ($omega^2$)
    $ omega^2 = n integral (overline(F)_n (x) - F(x))^2 d F(x) ->^d_(H_0) omega^2 $
]

#remark([Сложные гипотезы])[
  $X_1, dots, X_2 ~ G$ --- абсолютно непрерывное.
  $ H_0 : G in {G_theta | theta in Theta } $ 
  Оценим $hat(theta)_n$
  $ sqrt(n) sup_x |overline(F)_n (x) - G_(hat(theta)_n)| arrow.not K $
  Все плохо, потому что $overline(F)_n (x)$ и $G_(hat(theta)_n)$ зависимы 
  1. Если оценка сверхэффкетивна (т.е. $DD hat(theta)_n = o(1 / n)$) $==>$ можно подставить и ничего не будет зависеть.
  2. К-С, $omega^2$
    - Параметры сдвига-масштаба
    $ G_theta (x) = G_0 ((x - theta_1) / theta_2) $
    где $theta_1$ --- сдвиг, $theta_2$ --- масштаб
    - $hat(theta)_1, hat(theta)_2$ --- ОМП
    Тогда:
    $ D_n = sqrt(n) sup_x |overline(F)_n - G_(hat(theta)_n)| ->^d dots $
    не зависит от $hat(theta)$, зависит от $G_0$
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Критерий согласия
  - $H_0 : X_1, dots, X_n ~ P_0$, $H_1 : dots tilde.not P_0$. $nu_1, dots, nu_n$ --- частоты, $nu_i <-> p_i n$.
    $ bb(x)^2 (p) = sum_(i = 1)^k (nu_i - n p_i)^2 / (n p_i) ~_(H_0) chi^2_(k - 1) $
  - Вероятности не даны. Хотим найти $inf_p bb(x)^2 (p) ~_(H_0) chi^2_(k - 1 - d)$ где $d$ --- размерность параметра. Если нашли какой-то $p_0$, такой что $chi^2 (p_0) < z_(1 - alpha)$, то $inf_p dots$ точно меньше $z_(1 - alpha)$.
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Критерий однородности
  $X_1, dots, X_n ~ F$, $Y_1, dots, Y_m ~ G$. $H_0 : F = G$, $H_1 : F != G$. Частоты: $nu_(1, i)$--- первой выборки, $nu_(2, i)$ --- второй выборки. $nu_(dot, i) = nu_(1, i) + nu_(2, i)$. $hat(p)_i = nu_(dot, i) / (n + m)$
  $ bb(x)^2 = sum_(i = 1)^k (nu_(1, i) - n hat(p)_i)^2 / (n hat(p)_i) + sum_(i = 1)^k (nu_(2, i) - m hat(p)_i)^2 / (m hat(p)_i) ~_(H_0) chi^2_(k - 1) $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  $(X_1, Y_1), dots, (X_n, Y_n)$. $H_0$ : $X$ и $Y$ независимы. $X_i$ --- принимают $k$ значений, $Y_i$ --- принимает $m$ значений. Имеем частоты $nu_(i, j)$, $1 <= i <= m$, $1 <= j <= k$. Считаем суммы частот по строкам $nu_(i, dot)$ и столбцам $nu_(dot, j)$.
  $ hat(p)_(i, dot) = nu_(i, dot) / n quad hat(p)_(dot, j) = nu_(dot, j) / n $
  Тогда ожидаемая частота в клетке $i, j$: $n dot hat(p)_(i, dot) hat(p)_(dot, j)$.
  $ sum_(i, j) (nu_(i, j) - n dot hat(p)_(i, dot) hat(p)_(dot, j))^2 / (n dot hat(p)_(i, dot) hat(p)_(dot, j)) ~_(H_0) chi^2_((k - 1) (m - 1)) $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Гипотеза согласия для непрерывных распределений. $X_1, dots, X_n ~ F$. $H_0 : F = F_0$.
  1. $sup_t |F(t) - F_0(t)|$
    $ sqrt(n) sup_t |F(t) - F_0(t)| ->_(H_0) K $
    Имеем скачки в точках выборки. В $i$-той точке прыгаем с $(i - 1) / n$ на $i / n$ ступеньку. Супремум достигается в какой-то точке скачака. Вместо супремума будет искать $max_i {|F_0 (X_i) - (i - 1) / n|, |F_0 (X_i) - i / n|}$. Предполагаем что $X_i$ упорядочены.
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Гипотеза однородности для непрерывных распределений. $X_1, dots, X_n ~ F$, $Y_1, dots, Y_n ~ G$. $H_0 : F = G$.
  $ sqrt((n m) / (n + m)) sup_t |F_0 (t) - G_0 (t)| ->_(H_0) K $
]

#remark(fill: rgb("#87CEFA"), inset: 1em)[
  Альтернативная метрика
  $ n dot integral_(- infinity)^(+ infinity) (F(t) - F_0 (t))^2 d F(t) ->_(H_0) omega^2 $
  $ n dot integral_(- infinity)^(+ infinity) (F(t) - F_0 (t))^2 d F(t) = n omega^2_n = 1 / (12 n) + sum_(i = 1)^n (F(X_i) - (2i - i) / (2 n))^2 $
]
