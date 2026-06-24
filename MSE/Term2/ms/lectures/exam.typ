#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Математическая статистика],
  title: [Вопросы к экзамену],
  date: [25 июня],
  number: 0,
  program: "ITMO MSE y2025",
  with_outline: false,
  doc,
)


#show outline.entry: it => {
  link(it.element.location(), it.indented(text(fill: black, it.prefix()), text(fill: black, it.body())))
}

// #outline(title: [Вопросы])

#show heading.where(level: 1): it => {
  text(size: 16pt, weight: "bold", it)
}


#let theormin = [
  #h(-50pt - 7pt)#text(green)[`(a)`]#h(28pt + 7pt)
]

#let section(body) = [
  #heading(numbering: none)[#text(rgb(0, 0, 255), size: 16pt, weight: "bold")[#body]]
]

#let missing(content) = text(fill: red, weight: "bold", content)
#let extra = (note: none) => [#box(stroke: gray, inset: 4pt, baseline: 4pt)[#text(fill: gray, [*Не было*])]]
#let extra_ok = (note: none) => [#box(stroke: green, inset: 4pt, baseline: 4pt)[#text(fill: gray, [*Не было*])]]
#let slop = (note: none) => [#box(stroke: blue, inset: 4pt, baseline: 4pt)[#text(fill: blue, [*AI slop*])]]
#let canceled(content) = text(fill: gray, content)

#let extra-block = content => block(breakable: true, fill: luma(210), content, inset: (y: 1em, x: 0.5em))

= Понятие выборки. Генеральные и выборочные характеристики. #missing[Связь между ними]

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
  *Выборочная характеристика*. $Pi$ --- множество всех распределение на прямой. $T : Pi -> overline(RR) = RR union {+infinity}$ --- характеристика.

  $T(cal(P))$ --- *генеральная характеристика*

  $T(overline(cal(P))_n)$ --- *эмпирическая характеристика*
]

#extra-block[
  #example[
    Характеристики:
    - Математическое ожидание
      $ m_1 = T (cal(P)) = integral_RR z cal(P)(d z) $
      $
        overline(X) = overline(m_1) = T(overline(cal(P))_n) = integral_RR z overline(cal(P))_n (d z) = sum_(i = 1)^n X_i 1 / n = 1/n sum_(i = 1)^n X_i
      $
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
]

= Эмпирическое распределение
#definition[
  Эмпирическая функция распределения
  $ overline(F)_n (z) = overline(cal(P))_n ((-infinity, z)) = (\#{X_i < z}) / n $
]

#extra-block[
  #definition[
    $z_p$ --- квантиль уровня $p$, где $0 < p < 1$, если $F(z_p) = p$.
  ]

  #definition[
    $z_p$ --- *$p$-квантиль* для $cal(P)$, если $z_p = sup { z : F(z) < p }$. Эмпирические квантили $overline(z_p) = sup {z : overline(F_n)(z) <= p}$
  ]
]

= Выборочные характеристики как оценки генеральных. Свойства (состоятельность, несмещенность, асимптотическая несмещенность)
#definition[
  $overline(a)_n$ --- (выборочная характеристика) *состоятельная оценка генеральной*  характеристики $a$, если $overline(a)_n ->^PP a$.
]

#definition[
  Выборочная характеристика $overline(a)_n$ --- *несмещенная оценка* $a$, если $forall n med EE overline(a)_n = a_i$
]
#definition[
  Выборочная характеристика $overline(a)_n$ --- *ассимптотически несмещенная оценка* $a$, если $EE overline(a)_n ->_(n -> +infinity) a_i$
]

= Среднеквадратическое отклонение. Bias-Variance tradeoff. Исправленные (в смысле смещения) оценки
#remark[
  Когда есть $overline(a)_n ->^PP a$, то хотим знать скорость сходимости. Можем оценить через неравенство Чебышева
  $ PP(|overline(a)_n - a| < epsilon) <= (EE (overline(a)_n - a)^2) / epsilon^2 $
  $ EE (overline(a)_n - a)^2 = DD overline(a)_n + (EE overline(a)_n - a)^2 $
  где $EE overline(a)_n - a$ --- смещение (bias). $EE (overline(a)_n - a)^2$ --- среднеквадратическое отклонение
]

#remark[
  $ EE overline(s)_n^2 = dots = (n - 1) / n sigma^2 $
  $overline(s)_n^2$ --- смещенная, но асимптотически несмещенная.
  Смещение:
  $ EE overline(s)_n^2 - sigma^2 = -1/n sigma^2 $
  Иногда смещение убирают и рассматривают исправленную дисперсию
  $ tilde(s)_n^2 = 1 / (n - 1) sum_(i = 1)^n (X_i - overline(X))^2 = n / (n - 1) overline(s)_n^2 $
  Тогда получим состоятельную оценку $tilde(s)_n^2 ->^PP sigma^2$ и $EE tilde(s)_n^2 = sigma^2$, т.е. несмещенную. Убрали смещение, но важна еще и дисперсия:
  $ DD tilde(s)_n^2 = n^2 / (n - 1)^2 DD overline(s)_n^2 $
  Т.е. дисперсия (variance) увеличилась. На самом деле нас интересует сумма эти двух величин (смещение и дисперсия).
  $ EE (overline(s)_n^2 - sigma^2)^2 = DD overline(s)_n^2 + 1 / n^2 sigma^4 $
  $ EE (tilde(s)_n^2 - sigma^2)^2 = n^2 / (n - 1)^2 DD overline(S)_n^2 $
  Т.е. замена выборочной дисперсии на исправленную выборочную дисперсию приносит пользу только при маленьких размерах выборки.

  Это Bias-Variance tradeoff.
]

= Точечные оценки. Состоятельность. Несмещенность. Метод моментов (выборочных характеристик)
#definition[
  Оценка $hat(theta)$ --- любая (измеримая) функция от выборки, на зависящая от значения неизвестного параметра.
]

#definition[
  $hat(theta)_n$ --- *несмещенная* оценка параметра $theta$ если $EE hat(theta)_n = theta, forall theta in Theta$
]
#remark[
  Вообще говоря $hat(theta)_n$ это случайная величина которая имеет свое распределение, которое зависит от параметра $theta$
]

#definition[
  $hat(theta)_n$ *асимптотически* несмещена, если $EE hat(theta)_n ->_(n -> +infinity) theta, forall theta in Theta$
]

#definition[
  $hat(theta)_n$ --- *состоятельная* если $hat(theta)_n ->^PP_(n -> +infinity) theta, forall theta in Theta$
]

#remark[
  Метод выборочных характеристик (моментов). Есть выборочная характеристика $T: Pi -> overline(RR)$ (${cal(P)_theta} -> overline(RR)$). $T(cal(P)_theta) = h(theta) ==> theta = h^(-1)(T(cal(P)_theta))$
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

#remark[
  Оценки:
  1. Обычно смещены
  2. Часто состоятельны
  Если выборочная характеристика является состоятельной оценкой
  $ T(overline(cal(P))_n) ->^PP T(cal(P)) = h(theta) $
  Если $h^(-1) (theta)$ --- непрерывна и взаимно однозначна, то $hat(theta)_n$ --- состоятельная оценка.
]

= Метод максимума правдоподобия. Свойства
#remark("Метод максимального правдоподобия")[
  1. $X_1, dots, X_n ~ cal(P)_theta$ --- дискретное. Т.е. для каждого значения вероятность $p_theta (y_i)= (1 - theta)^(1 - y) theta^y$. Можем посчитать вероятность что получим именно эти числа
    $ PP(X_1, dots, X_n) = product p_theta (x_i) = L(theta) $
    где $L$ --- функция правдоподобия
    $ cal(l)(theta) := sum_(i = 1)^n log p_theta (x_i) $
    $ hat(theta)_n = "argmax"_theta L(theta) = "argmax"_theta l(theta) $
    Хотим найти решение $hat(theta)'_n = 0$.

    $
      L(theta) = product p_theta (x_i) = theta^(X_1 + dots + X_n) (1 - theta)^(n - X_1 - dots - X_n) = theta^(n overline(X)) (1 - theta)^(n (1 - overline(X))) \
      l(theta) = n overline(X) log theta + n (1 - overline(X)) log (1 - theta) \
      hat(theta)'_n = (n overline(X)) / theta - (n (1 - overline(X))) / (1 - theta) = 0 ==> theta = overline(X)
    $
  2. $cal(P)_theta$ --- абсолютно непрерывное. $p_theta (y)$ --- плотность
    $ L(theta) = product_(i = 1)^n p_theta (X_i) $
]

#remark[
  Рассмотрим
  $ l_n (theta) = 1 / n sum_(i = 1)^n log p_theta (X_i) $
  $"argmax" l_n (theta) = hat(theta)_n$ и $l_n (theta) ->^PP_(n -> +infinity) EE log p_theta (X_i)$, тогда хотим замкнуть диаграмму $theta^* = "argmax" EE log p_theta (X_i)$. Нужно чтобы $theta^* = {theta_0}$. Рассмотрим
  $ l(theta) = 1/n sum_(i = 1)^n log p_theta / p_(theta_0) (X_i) $
  $ EE l(theta) (X) = integral log p_theta / p_(theta_0) (y) p_theta (y) d y <= 0 $
  Из этого следует что
  1. $theta_0 in Theta^*$, т.е. интеграл равняется $0$.
]

#statement[
  Пусть $theta_1 != theta_2 ==> p_(theta_1) != p_(theta_2)$. Тогда $Theta^* = {theta_0}$.
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

= Неравенство Рао-Крамера. Эффективные и сверхэффективные оценки
#theorem("Неравенство Рао-Крамера")[
  Пусть $hat(theta)_n$ --- существует $DD hat(theta)_n$, $b_n (theta) = EE (hat(theta)_n - theta)$. Тогда при выполнении условий регулярности
  $
    DD hat(theta)_n + b_n^2 (theta_0) = EE (hat(theta)_n - theta)^2 >= (1 + b'_n (theta_0))^2 / (n I(theta_0)) + b_n^2 (theta_0)
  $
]

#corollary[
  $ DD hat(theta)_n >= (1 + b'_n (theta_0))^2 / (n I (theta_0)) $
  Для несмещенных
  $ DD hat(theta)_n >= 1 / (n I(theta_0)) $
]

#definition[
  $hat(theta)_n$ --- (R-)эффективная если в неравенстве Рао-Крамера имеет место равенство $forall theta_0$.
  Для несмещенных это значит
  $ DD hat(theta)_n = 1 / (n I(theta_0)) $
]

#definition[
  $hat(theta)_n$ --- ассимптотически (R-)эффективной если в неравенстве Рао-Крамера достигается равенство при $n -> +infinity$.
]

#statement[
  ОМП --- ассимптотически (R-)эффективные
]


#example[
  Для равномерного распределения ОМП $hat(theta)_n = max X_i$
  $ DD hat(theta)_n = cal(O)(1 / n^2) $
  Дисперсия убывает быстрее чем граница в неравенстве Рао-Крамера. Таких оценки называются *сверхэффективными*.
]

= Интервальное оценивание. Понятие доверительного интервала. Распределения, связанные с нормальными. Построение доверительных интервалов через центральные статистики
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

#definition[
  Случайная величина $g(X_1, dots, X_n; theta)$ --- центральная статистика для $theta$
  1. Распределение $g(X_1, dots, X_n; theta)$ --- не зависит от $theta$
  2. $G_n$ --- функция распределения центрального распределения --- непрерывна
  3. $forall z_1, z_2 : z_1 < g(X_1, dots, X_n; theta) < z_2$, $exists f_1, f_2 : forall theta:$
    $ f_1(X_1, dots, X_n; z_1, z_2) < theta < f_2(X_1, dots, X_n; z_1, z_2) $
]

#remark[
  1. Фиксируем $gamma$
  2. Выбираем $z_1, z_2$: $G_n (z_2) - G_n (z_1) = gamma$
  3. $
      gamma = G_n (z_2) - G_n (z_1) = PP(z_1 < g(X_1, dots, X_n; theta) < z_2) = \
      = PP(f_1(X_1, dots, X_n; z_1, z_2) < theta < f_1(X_1, dots, X_n; z_1, z_2))
    $
]

#statement[
  1. $X_1, dots, X_k ~ cal(N)(0, 1)$. Тогда $X_1^2 + dots + X_k^2 ~ chi^2_k = Gamma(k / 2, 1 / 2)$
  2. $X_1, dots, X_n$ --- н.о.р.с.в. $cal(N)(a, sigma^2)$. Тогда $sqrt(n) (overline(X) - a) / sigma ~ cal(N)(0,1)$ и $sqrt(n - 1) (overline(X) - a) / overline(s)_a ~ t_(n - 1)$ --- распределение Стьюдента с $n - 1$ степенью свободы
  3. $X_1, dots, X_n$ --- н.о.р $cal(N)(a, sigma^2)$
    $ sum_(i = 1)^n (X_i - a)^2 / sigma^2 ~ chi^2_n $
    $ sum_(i = 1)^n (X_i - overline(X))^2 / sigma^2 ~ chi^2_(n - 1) $
]
= Точные доверительные интервалы для среднего и дисперсии в нормальной модели

#remark[
  1. $X_1, dots, X_n ~ cal(N)(theta, sigma^2)$
    $ g(X_1, dots, X_n; theta) = sqrt(n) (overline(X) - theta) / sigma ~ cal(N)(0, 1) $
  2. $X_1, dots, X_n ~ cal(N)(theta, *)$ (дисперсия неизвестна)
    $ g(X_1, dots, X_n; theta) = sqrt(n - 1) (overline(X) - theta) / overline(s)_n ~ t_(n - 1) $
    Т.е. $overline(X) plus.minus z_((1 + alpha) / 2) overline(s)_n / sqrt(n - 1)$, где $z$ --- квантили распределения Стьюдента $t_(n - 1)$.
  3. $X_1, dots, X_n ~ cal(N)(a, theta)$
    $ g(X_1, dots, X_n; theta) = sum_(i = 1)^n (X_i - a)^2 / sigma^2 ~ chi^2_n $
    Пусть $breve(s)_n^2 := sum_(i = 1)^n (X_i - a)^2$. Тогда
    $ z_1 < (n breve(s)_n^2) / theta < z_2 $
  4. $X_1, dots, X_n ~ cal(N)(*, theta)$
    $ g(X_1, dots, X_n; theta) = (n overline(s)_n^2) / theta ~ chi^2_(n - 1) $
]
= Асимптотические доверительные интервалы. Построение асимптотических доверительных интервалов для среднего: в общем случае, частный случай выборки из биномиального распределения (вероятность успеха в испытаниях Бернулли)
#theorem("ЦПТ")[
  $X_1, dots, X_n$ --- н.о.р $DD X_i = sigma^2 < +infinity$, $EE X_i = a$
  $ sqrt(n) (overline(X) - a) / sigma ->^d cal(N)(0, 1) $
  $ PP(z_1 < sqrt(n) (overline(X) - a) / sigma < z_2) -> Phi(z_2) - Phi(z_1) $
]
#corollary([Лемма Слуцкого])[
  $ sqrt(n) (overline(X) - a) / overline(s)_n ->^d cal(N)(0, 1) $
]

#example[
  $X_1, dots, X_n$ --- испытания Бернулли ($p$)
  $ sqrt(n) (overline(X) - p) / sqrt(p (1 - p)) ->^d cal(N)(0, 1) $
  $ z_1 < sqrt(n) (overline(X) - p) / sqrt(p (1 - p)) < z_2 $
  Используя лемму Слуцкого
  $ z_1 < sqrt(n) (overline(X) - p) / sqrt(overline(X) (1 - overline(X))) < z_2 $
  где $z$ --- квантили $cal(N)(0, 1)$.
]
#example[
  Общий случай. $X_1, dots, X_n$, $EE X_i = a$, $DD X_i = sigma^2 < +infinity$
  $ overline(X) plus.minus z_((1 + gamma) / 2) overline(s)_n / sqrt(n) $
  --- асимптотический доверительный интервал для $a$, где $z$ --- квантили $cal(N)(0, 1)$.
]

= Дельта-метод
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
  $
    sqrt(n) (overline(X)_n - mu) ->^d cal(N)(0, sigma^2) ==> \
    ==> sqrt(n) (g(overline(X)_n) - g(mu)) ->^d cal(N)(0, sigma^2 g'(mu)^2)
  $
  при $g'(mu) != 0$
]

#extra-block[
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
]
= Преобразования, стабилизирующие дисперсию
#example[
  $X_1, dots, X_n ~ cal(N)(0, sigma^2)$. Пусть $Y_i := X_i^2$, тогда
  $ EE Y_i = EE X_i^2 = sigma^2 quad DD Y_i = DD X_i^2 = 2 sigma^4 $
  Применим ЦПТ для $Y_i$:
  $ sqrt(n) (1/n sum_(i = 1)^n X_i^2 - sigma^2) ->^d cal(N)(0, 2 sigma^4) $
  $ sqrt(n) (1/n sum_(i = 1)^n X_i^2 - sigma^2) / (sqrt(2) sigma^2) ->^d cal(N)(0, 1) $

  Попробуем найти такую $g$, что $2 (g'(sigma^2))^2 sigma^4 = "const"$ (по $sigma^2$). Возьмем $g(t) = log t$. Тогда
  $ sqrt(n) (log(1/n sum_(i = 1)^n X_i^2) - log sigma^2) ->^d cal(N)(0, 2) $
  Т.е. центральная статистика
  $ sqrt(2n) (log overline(Y)_n - log sigma^2) $
  Доверительный интервал для $sigma^2$
  $ e^(log overline(Y)_n plus.minus z_((1 + gamma) / 2) / sqrt(2n)) $
]

#remark[
  Зачем это нужно. Пусть имеем
  $ sqrt(n) (overline(X)_n - mu) ->^d cal(N)(0, sigma^2 (mu)) $
  Тогда центральная статистика
  $ z_1 < sqrt(n) (overline(X)_n - mu) / sqrt(sigma^2 (mu)) < z_2 $
  Решать относительно $mu$ сложно
]

#extra-block[
  #example[
    $X_1, dots, X_n$ --- испытания Бернулли ($p$). $sigma^2 (p) = p (1 - p)$. Хотим взять функцию такую что $g'(p)^2 p (1 - p) = "const"$:
    $
      g'(p) = 2 / sqrt(p (1 - p)) ==> g(p) = 2 integral (d p) / sqrt(p (1 - p)) = integral (d u) / sqrt(1 - u^2) = 2 arcsin u = 2 arcsin sqrt(p)
    $
    Получили что
    $ 2 sqrt(n) (arcsin sqrt(overline(X)_n) - arcsin sqrt(p)) ->^d cal(N)(0, 1) $
  ]
  #example[
    $X_1, dots, X_n ~ "Pois"(lambda)$. Нужно $g'(lambda)^2 dot lambda = "const" ==> g(t) = 2 sqrt(t)$. Тогда
    $ 2 sqrt(n) (sqrt(overline(X)_n) - sqrt(lambda)) ->^d cal(N)(0, 1) $
  ]
]
= Общие подходы к построению статистических критериев. Понятие мощности, ошибок первого и второго рода
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

#definition[
  - *Ошибка I рода*: $phi$ отвергает гипотезу $H_0$ когда она верна. $phi(X_1, dots, X_n) = 1$, но $X_1, dots, X_n ~ P_0 in cal(P)_0$.
    $ alpha_"I" = P((X_1, dots, X_n) in S | P_0 in cal(P)_0} = PP(H_1 | H_0) $
  - *Ошибка II рода*: $phi$ принимает $H_0$ когда она неверна. $phi(X_1, dots, X_n) = 0$, но $X_1, dots, X_n ~ P_0 in.not cal(P)_0$.
    $ alpha_("II") = P((X_1, dots, X_n) in D | P_0 in.not cal(P)_0) = PP(H_0 | H_1) $
]

#definition[
  *Мощность критерия*: $beta = 1 - alpha_("II")$.
]

#extra-block[
  #example[
    $cal(P) = {cal(N)(a_1, sigma^2), cal(N){a_2, sigma^2)}$. $H_0 : a = a_1$, $H_1 : a = a_2$. Пусть $z = sqrt(n) (overline(X) - a_1) / sigma$. Если верна $H_0$, то $z ~_(H_0) cal(N)(0, 1)$. Пусть $phi(X_1, dots, X_n) = cases(0"," |z| < 1.96, 1","#[иначе])$
    $
      alpha_I = PP(H_1 | H_0) = PP(phi(X_1, dots, X_n) = 1 | a = a_1) \
      = PP(|z| >= 1.96 | z ~ cal(N)(0, 1)) = Phi(-1.96) + (1 - Phi(1.96)) = 0.05
    $
    $ z = sqrt(n) (overline(X) - a_1) / sigma = sqrt(n) (overline(X) - a_2) / sigma + sqrt(n) (a_2 - a_1) / sigma $
    Если верна $H_1$, тогда:
    $ z ~_(H_1) cal(N) (sqrt(n) (a_2 - a_1) / sigma, 1) =: Phi_1 $
    $ alpha_(I I) = PP(|z| < 1.96, z ~ Phi_1) = Phi_1(1.96) - Phi_1(-1.96) $
    $ Phi_1(z) = Phi(z - sqrt(n) (a_2 - a_1) / sigma) $
  ]
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
= Связь проверки статистических гипотез и построения доверительных интервалов. Понятие p-значения. Одновыборочный t-критерий. Критерий Фишера. Асимптотические критерии. Проверка гипотез относительно значения среднего (одновыборочный z-критерий, критерий пропорций)
#remark[
  Доверительные интервалы vs проверка гипотез. $X_1, dots, X_n ~ cal(P)_(theta_0)$
  $ PP ((hat(theta)_n^-, hat(theta)_n^+) in.rev theta_0) = gamma $
  $H_0 : theta = theta^*$. Схема построения
  1. Строим доверительный интервал $(hat(theta)_n^-, hat(theta)_n^+)$
  2. Проверяем $theta^* in (hat(theta)_n^-, hat(theta)_n^+)$.
  $ alpha_I = PP (theta^* in.not (hat(theta)_n^-, hat(theta)_n^+) | theta^* = theta_0) = 1 - gamma $
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
  $ z = sqrt(n) (overline(X) - a_0) / tilde(s)_n $
  z-критерий предписивыет использовать критическую область с квантилями из нормального распределения $S_alpha^cal(N) : (-infinity, z_(alpha / 2)) union (z_(1 - alpha / 2), +infinity)$. *Ошибка*: давайте возьмем квантили Стьюдента.
]
= Двухвыборочный t-критерий (разные вариант, в т.ч. критерий Уэлча). Критерий Фишера. Асимптотические критерии. Проверка гипотез относительно значения среднего ( двухвыборочный z-критерии, критерий пропорций). Критерий хи-квадрат. Критерий хи-квадрат и выборка из абсолютно-непрерывного распределения
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
  $
    T = (overline(X)_1 - overline(X)_2) / sqrt(overline(s)_n^2 / n + overline(s)_m^2 / m) [~ dots] ->^d_(n -> +infinity \ m ->+infinity) cal(N)(0, 1)
  $
]

#extra-block[
  #remark[
    - $X_1^((1)), dots, X_n^((1)) ~ B(p_1)$
    - $X_1^((2)), dots, X_n^((2)) ~ B(p_2)$
    $ H_0 : p_1 = p_2 quad H_1 : p_1 != p_2 $
    $ z = (overline(X)_1 - overline(X)_2) / (sqrt(1 / m + 1 / n) sqrt(tilde(p) (1 - tilde(p)))) ->^d_(H_0) cal(N)(0, 1) $
    где $tilde(p) = (n overline(X)_1 + m overline(X)_2) / (n + m)$
  ]
]

#remark([Двухвыборочный z-критерий])[
  - $X_1^((1)), dots, X_n^((1))$, $DD X_i^((1)) < +infinity$, $EE X_i^((1)) = a_1$
  - $X_1^((2)), dots, X_n^((2))$, $DD X_i^((2)) < +infinity$, $EE X_i^((2)) = a_2$
  $ H_0 : a_1 = a_2 quad H_1 : a_1 != a_2 $
  $ z = (overline(X)_1 - overline(X)_2) / sqrt(overline(s)_n^2 / n + overline(s)_m^2 / m) ->^d_(H_0) cal(N)(0, 1) $
]

= Критерий хи-квадрат и выборка из абсолютно-непрерывного распределения. Критерий хи-квадрат и оценки параметров (проверка сложных гипотез). Критерий хи-квадрат для независимости. Критерии согласия и проверка сложных гипотез. Критерии согласия: критерий Колмогорова-Смирнова, критерий Крамера-Смирнова-фон Мизеса

#remark([Критерий согласия])[
  1. Хи-квадрат
    - $X_1, dots, X_n$ --- выборка, $X_i$ --- дискретная. $x_j$ --- исходы $j = 1 dots m$. $PP(X = x_j) = p_j$, $sum p_j = 1$. Дискретное распределение целиком определяется $(x_j, p_(overline(c))), j = 1 dots m$.
    $ H_0 : #text[все] p_j = PP(X = x_j) quad H_1 : exists j : p_j != PP(X = x_j) $
    Есть набор $O_j = \#{X_i = x_j}, j = 1 dots m$ --- частоты (сколько раз встретился исход $j$). Если верна $H_0$ то $x_j$ встретится $EE O_j = n dot p_j$ раз ($H_0 : O_j / n ~ B(p_j)$).

    $ XX^2 = sum_(j = 1)^m (O_j - EE O_j)^2 / EE O_j = sum_(j = 1)^m (O_j - n p_j)^2 / (n p_j) ->^d_(H_0) chi^2_(m - 1) $
    Это норм если $n p_j > 5$.
]
#remark[
  Если $n p_j < 5$. Можем сгруппировать некоторые вероятности. $(x_(j_1), p_(j_1)), (x_(j_2), p_(j_2)) |-> ({x_(j_1), x_(j_2)}, p_(j_1) + p_(j_2))$.
]

#remark[
  Превращение непрерывного распределения в дискретное. $(-infinity, +infinity) = union.big.sq_(i = 1)^m (a_i, b_i)$
  $ p_i = PP(X in (a_i, b_i)) = integral_(a_i)^(b_i) p(x) d x quad O_i = \#{X_j in (a_i, b_i)} $

  Будем разбивать чтобы все $p_i$ были равны и чтобы $n p_i > 5$, т.е. $n / m > 5$.
]

#remark[
  Хотим проверить сложную гипотезу. $p_i = p_i (theta)$
  $ XX^2 = XX^2 (theta) = sum_(i = 1)^m (O_i - n p_i (theta))^2 / (n p_i (theta)) $
  $ H_0 : #text[все $p_i (theta_0) = PP(X = x_j)$ для некоторой $theta_0$] $
  $hat(theta)_n$ --- оценка параметра
  $ XX^2 (hat(theta)_n) = sum_(i = 1)^m (O_i -n p_i (hat(theta)_n))^2 / (n p_i (hat(theta)_n)) $
  1. $tilde(theta)_n = "argmin" XX^2 (theta)$
    $ XX^2 ( tilde(theta)_n) ->^d_(H_0)chi^2_(m - 1 - p) $
    где $p = dim Theta$
  2. $hat(theta)_n$ --- ОМП
    $ XX^2 (hat(theta)_n) ->^d_(H_0)chi^2_nu $
    где $m - 1 - p <= nu <= m$
]

#remark([Хи-квадрат и независимость])[
  $(X_i, Y_i)$ --- дискретное
  $ p_(i j) = PP(X = x_i, Y = y_j) $
  $X,Y$ --- независимые $<==> p_(i j) = PP(X = x_i) dot PP(Y = y_i)$. $O_(i, j) = \#{X = x_i, y = y_j}$. Таблица $2 times 2$.
  $ EE O_i = n dot p_(i j) = n dot p_i dot p'_j $
  $ H_0 : #text[$X$ и $Y$ независимы $<==>$ все $p_(i j) = p_i dot p_j$] $ 
  $ EE_(i j) = sum_(k = 1)^m O_(i k) dot sum_(k = 1)^m O_(k j) = n hat(p)_i hat(p)'_j $
  $ XX^2 = sum_(i = 1)^(m_1) sum_(j = 1)^(m_2) (O_(i j) - EE_(i j)) / EE_(i j) ->^d_(H_0) chi^2_((m_1 - 1) (m_2 - 1)) $
]

#remark([Критерий согласия и абсолютно непрерывные распределения])[
  $X_1, dots, X_n ~ G(x)$ --- абсолютно непрерывное.
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
