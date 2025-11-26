#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

// TODO: Move to common
#import "@preview/h-graph:0.1.0": enable-graph-in-raw, polar-render
#show raw.where(lang: "graph"): enable-graph-in-raw(polar-render)

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 11],
  date: [26 ноября],
  number: 11,
  doc
)

= Закон больших чисел
 
#theorem([Закон больших чисел (ЗБЧ)])[
$xi_1, xi_2, dots$ --- попарно некоррелируемы. $exists M : forall i quad DD xi_i <= M$. Пусть $S_n = xi_1 + dots + xi_n$. Тогда
$ S_n / n - EE S_n / n -->^PP 0 $
]
#proof()[
  $forall epsilon > 0 quad PP(|S_n / n - EE S_n / n| > epsilon) -->_(n -> +infinity) 0?$
  $ PP(|S_n / n - EE S_n / n| > epsilon) <=#pin(1) (DD S_n / n) / epsilon^2 = (DD S_n) / (n^2 epsilon^2) <=#pin(2) (n M) / (n^2 epsilon^2) --> 0 $
  // FIXME: 
  // #pinit-point-from(1)[По неравенству Чебышева]
  $ DD S_n = DD (xi_1 + dots + xi_n) = sum_(i = 1)^n undershell(DD xi_i, = M) + 2 sum_(i < j) undershell("cov" (xi_1, xi_j), = 0) <= #pin(3) n dot M $
  // FIXME:
  // #pinit-line(3, 1)
]

#corollary([ЗБЧ в форме Чебышева])[
  $xi_1, xi_2, dots$ -- н. о. р. с. в. $EE xi_i = m quad DD xi_i = sigma^2 < +infinity$. Тогда
  $ S_n / n -->^PP m $
]
#proof()[
  $ EE S_n / n = 1/ n EE S_n = 1/n EE (xi_1 + dots + xi_n)  = (n m) / n = m $
]

#theorem([Усиленный закон больших чисел (УЗБЧ)])[
  $x_1, xi_2, dots$ --- независимые. $exists M : forall i quad EE xi_i^4 <= M$. Тогда
  $ S_n / n - EE S_n / n --> 0 #text[п.н.] $
]

#theorem([Центральная предельная теорема (ЦПТ)])[
  $xi_1, xi_2, dots$ --- н. о. р. с. в. $EE xi_i = m quad DD xi_i = sigma^2 quad (0 < sigma^2 < +infinity)$. Тогда
  $ (S_n - n m) / sqrt(n sigma^2) -->^d cal(N)(0, 1) $
  т.е. $forall x in RR quad PP((S_n - n m) / sqrt(n sigma^2) <= x) --> Phi(x)$
]

#remark()[
  $(S_n - EE S_n) / sqrt(DD S_n) = (S - n m) / sqrt(n sigma^2)$. Отцентрировали и отнормировали.
]

#remark()[
  На самом деле
  $ PP( (S_n - n m)  / sqrt(n sigma^2) <= x) arrows Phi(x) $
  Это равномерная сходимость. Можно заменить на сходящуюся последовательность $x_n -> x$.
]

#corollary()[
  $xi_1, xi_2, dots$ --- независимые. $xi_1 ~ B(p)$ --- распределение Бернулли. $EE xi_i = p quad DD xi_i = p q$. $xi_1 + dots + xi_n$ --- количество успехов в схеме Бернулли.
  $ (S_n - n p) / sqrt(n p q) $
]

= Теория графов

#definition()[
  *Граф* $G$ --- это пара множеств $V(G)$ --- множество вершин, $E(G)$ --- множество ребер. Ребро будет понимать как пару вершин $e = u v quad e in E(G), u,v in V(G)$.
]

Если порядок вершин важен, то $G$ --- ориентированный граф. Если не важен, то неориентированный. Если не сказано, то считаем $G$ --- неор.


#definition()[
  Если $exists e_1, e_2 in E(G) : e_1 = u v quad e_2 = u v$, то в графе есть *кратные* ребра, а сам $G$ --- *мультиграф*.
]

#definition()[
  Если $exists e = u u$, то $e$ --- петля, а сам граф $G$ --- псевдограф
  // ```graph
  // #scl: 0.5;
  // 1-2, 3, 4
  // ```
]

#definition()[
  Если вершина $u$ является концом ребра $e$, то $u$ и $e$ *инцидентны*
]

#definition()[
  Если $u$ и $v$ инцидентны какому-то $e$, то эти вершины смежны
]

#definition()[
  Если $e_1$ и $e_2$ инцидентны какой-то $v$, то эти ребра смежны
]

#definition()[
  *Степенью* вершины $b$ называется количество ребер инцидентных ей. Петля считается два раза.
]

#symb()[
  $"deg"(v)$; $d(v)$
]

#statement()[
  $sum_(v in V(G)) "deg"(v) = 2 dot |E(G)|$
]
#proof()[
  Каждое ребро увеличивает и левую и правую часть на $2$.
]

#remark()[
  Если $G$ -- орграф. $v in V(G)$, $"indeg"(v)$ --- количество входящих ребер в $v$, $"outdeg"(v)$ --- исходящих.
]

#lemma([о рукопожатиях])[
  В любом графе четное количество вершин нечетной степени.
]
#proof()[
  Очевидно из $2 dot |E(G)| = sum_(v in V(G)) "deg"(v)$.
]

#definition()[
  Если $"deg"(v) = 0$, то $v$ --- изолированная вершина. Если $"def"(v) = 1$ то $v$ --- висячая вершина.

]
#symb()[
  $max_(v in V(G)) "deg"(v) eq.colon Delta(G)$
]
#symb()[
  $min_(v in V(G)) "deg"(v) eq.colon delta(G)$
]

#definition()[
  Последовательность вершин и ребер $v_1 e_1 v_2 e_2 dots e_(n - 1) v_n$, где $v_i in V(G), e_i in E(G)$ и $forall i in [1; n - 1] quad e_i = v_i v_(i + 1)$ называется *маршрутом*. Длина по количеству ребер.

  Если $v_1 = v_n$, то маршрут замкнутый.
]

#definition()[
  Путь в графе $G$ --- маршрут у которого все ребра уникальны.
]

#definition()[
  Если начало пути совпадает с концом, то такой путь называется циклом.
]

#definition()[
  Если в пути все вершины уникальны, то такой путь является простым.
]

#definition()[
  Если в цикле все вершины уникальны (за исключением $v_1 = v_n$), то такой цикл называется простым.
]
