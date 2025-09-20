#import "../../../../other/typst/lecture.typ": *
#show: doc => conf(
  title: [Лекция 3],
  date: [24 февраля],
  doc
)

= Смешанные стратегии
Случайность -- остутствие системы. Вероятность -- "частота".

Грубо говоря, разыгрывание трех стратегий с равной вероятностью = применение с одинаковой
частотой, т.е. каждую стратегию вы используете *приблизительно* $n/3$ раз

#definition[
*Смешанные стратегии* -- вероятностное распределение на множестве его чистых стратегий.
$ x = vec(x_1, dots.v, x_m), x_i >= 0, sum_(i = 1)^m x_i = 1 $
]
Ожидаемый выигрыш 1 игрока
$ K_1 (x, y) = x^T A y = sum_(i = 1)^m sum_(j = 1)^n a_(i j) x_i y_j $

#example[
#align(center)[
  #tablex(
    columns: 4,
    auto-lines: false,
    align: center + horizon,
    // typstfmt::off
    (), (), vlinex(), (), (),
    [], colspanx(3)[Жена], (), (),
    rowspanx(3)[Муж], [], [Ф], [Б],
    hlinex(),
    (), [Ф], [$2, 3$], [$0, 0$],
    (), [Б], [$1, 1$], [$3, 2$],
    // typstfmt::on
  )
]

Мужа $eta^* = (q^*, 1 - q^*)$ \
Жены $sigma^* = (p^*, 1 - p^*)$

$ K_M (S_М^1, sigma^*) = K_М (S_М^2, sigma^*) $
где $S_М^1$ -- Муж на Ф, $S_М^2$ -- Муж на Б

$ М = mat(2, 0; 1, 3) quad Ж = mat(3, 0; 1, 2) $
$ mat(1, 0) mat(2, 0; 1, 3) vec(p^*, 1 - p^*) = (0, 1) mat(2, 0; 1, 3) vec(p^*, 1 - p^*) $
$ 2p^* = 3 - 2p^* => p^* = 3/4 => sigma^* = (3/4, 1/4) $
$ K_Ж (eta^*, S_Ж^1) = K_Ж (eta^*, S_Ж^2) => eta^* = (1/4, 3/4) $
]

// TODO: It's corollary
#remark[
#enum(
  numbering: "1)",
  enum.item(2)[
   Условие общего положения: $a != e, c != g, b != d, h != f$ 
   #enum(
     numbering: "i)",
   )
  ]
)
]

#task[
  #tablex(
    columns: 3,
    auto-lines: false,
    align: center,
    // typstfmt::off
    (), vlinex(), (), (),
    [(R, C)], [1], [2],
    hlinex(),
    [1], [$(5, 0)$], [$(3, 1)$],
    [2], [$(5, 2)$], [$(3, 0)$],
    // typstfmt::on
  )
  $sigma_R = (p, 1 - p) quad sigma_C = (q, 1 - q)$
  $ K_R (sigma_R, sigma_C) = mat(p, 1 - p) mat(5, 3; 5, 3) vec(q, 1 - q) = 3 - 2q $
  не зависит от $sigma_R ==> forall sigma_R$ является наилучшим ответом на $forall sigma_C$ 
  $ K_C (sigma_R, sigma_C) = p + q (2 - 3p) $
  увеличивание $q$ $=>$ возрастает при $p < 2/3$, убывает при $p > 2/3$, не зависит от $q$ при $p = 2/3$. Тогда можем сказать что
  - $p < 2/3$: $(p, 1 - p), (1, 0)$
  - $p > 2/3$: $(p, 1 - p), (0, 1)$
  - $p = 2/3$: $(2/3, 1/3), (q, 1 - 1) q in [0, 1]$
]

== О смешанных равновесиях в симметричных играх
Симметричные игры -- игры, задаваемые такими квадратными матрицами $A$ и $B$, что $a_(i j) = b_(i j) forall i,j$.
Симметричный профиль $(sigma, sigma)$, где $sigma = (p_1, ..., p_m)$ и $p_j != 0 forall j$, является симметричными равновесием Нэша
для симметричной игры, заданной $(m times m)$-матрицей $A$ ттогда, когда
$ A dot sigma = lambda vec(1, 1, 1), quad lambda = K(sigma, sigma) $
В частности, если $A$ невырождена, то
$ sigma = lambda dot A^(-1) vec(1, 1, 1) $ <sim-loc-1>
и значит, возможно лишь одно такое равновесие, и оно существует ттогда, кода координаты @sim-loc-1 положительны

#example[
  $ A = mat(-a, 1, -1; -1, -a, 1; 1, -1, -a) quad a != 0 $
  #enum(
    numbering: "(i)",
    [
      $
      (sigma, sigma), sigma = (p_1, p_2, p_3), p_j > 0, sum p_j = 1 \
      det A = -a (a^2 + 3) != 0 \
      sigma = lambda A^(-1) vec(1, 1, 1) \
      A^(-1) = (-1)/(a(a^2 + 3)) mat(1 + a^2, 1 + a, 1 - a; 1 - a, 1 + a^2, 1 + a; 1 + a, 1 - a, 1 + a^2) \
      lambda = K(sigma, sigma) = mat(p_1, p_2, p_3) A vec(p_1, p_2, p_3) = -a (p_1^2 + p_2^2 + p_3^2) \
      $
      $
      vec(p_1, p_2, p_3) & = -a (p_1^2 + p_2^2 + p_3^2) (-1)/(a (a^2 + 3)) 
        mat(1 + a^2, 1 + a, 1 - a; 1 - a, 1 + a^2, 1 + a; 1 + a, 1 - a, 1 + a^2) vec(1, 1, 1) \
      & =  vec(p_1^2 + p_2^2 + p_3^2, p_1^2 + p_2^2 + p_3^2, p_1^2 + p_2^2 + p_3^2) = vec(p_1, p_2, p_3) => \
      & => #stack(spacing: 3pt, [$p_1 = p_2 = p_3$], [$p_1 + p_2 + p_3 = 1$]) => p_1 = p_3 = p_3 = 1/3
      $
      Ответ: $sigma^* = (1/3, 1/3, 1/3)$
    ],
    [
      $sigma = (p, 1 - p, 0)$
      $
        // FIXME: double tilde
        tilde(A) = mat(-a, 1; -1, -a) & => tilde(tilde(A)) = mat(1 - a, 2; 0, 1 - a) => \
        & => sigma_1^* = ((a + 1)/(2a), (a - 1)/(2a), 0)
      $
      $
        K(sigma_1^*, sigma_1^*) = - 1 / (2a) (a^2 + 1) quad K(3, sigma_1^*) = 1/a \
      $
      $(sigma_1^*, sigma_1^*)$ равновесие $<=>$ $-1/(2a) (a^2 + 1) >= 1/a$ $=> a < -1$ \
      Ответ:
      $
      cases(
        reverse: #true,
        display(sigma_1^* = ((a + 1)/(2a), (a - 1)/(2a), 0)),
        display(sigma_2^* = ((a -1)/(2a), 0, (a + 1)/(2a))),
        display(sigma_3^* = (0, (a + 1)/(2a), (a - 1)/(2a))),
      ) a < - 1 \
      sigma_4^* = (1/3, 1/3, 1/3), a != 0
      $
    ]
  )
]
