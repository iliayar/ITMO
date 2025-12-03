#import "common.typ": *

// TODO: Move to common
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge, shapes

#show: doc => hw(12, doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution()[
  Ну умаляя общности предположим что граф содержит две компоненты связности $A$ и $B$. Тогда никакая $u in V(A)$ не смежна ни с какой $v in V(B)$. Тогда в $overline(G)$ любая вершина $v in V(A)$ смежна с любой $v in V(B)$. Тогда между двумя вершинами $u_1, u_2 in V(A)$ есть путь $u_1 e_1 v e_2 u_2$, где $v in V(B)$. Т.е. между любыми двумя вершинами есть путь $==>$ связный.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution()[
  Пусть нельзя, значит удалил мост. Значит степень инцидентных ему вершим уменьшилась на $1$ и получилось две компоненты. В каждой компоненте все вершины кроме одной имеют степень $100$, а одна имеет степень $99$. Но по теореме о рупопожатиях таких подграфов быть не может: нечетное количество вершин с нечетной степенью. Противоречи. Значит связность сохранилась.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution()[
  Покажем как провести ребра в графе так чтобы условие $"outdeg"(x) = "indeg"(x)$ выполнялось.
  1. Пронумеруем вершины в каком-то порядке от $1$ до $n$
  2. Для наглядности построим $(n + 1) / 2$ циклических сдвигов $c^i$, $i in [0; (n - 1) / 2]$.
  3. Проведем ребра $c^i_j -> c^(i + 1)_j$ для всех $j$ и $i in [0; (n - 1) / 2)$, т.е. из $v_j$ в $v_(j + i mod n)$ для всех $j in [0; n)$ и $i in [1; (n - 1) / 2]$.
  Получается для каждой вершины провели $(n - 1) / 2$ ребер из нее и $(n - 1) / 2$ ребер в нее.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 4))[]
#solution()[
  #enum(numbering: "a)")[
  #grid(
    columns: (3fr, 1fr, 1fr),
    gutter: 10pt,
    [
      #align(left)[
        Контрпример. В первом случае граф двудольный, во втором нет, т.к. есть цикл нечетной длины.
        Значит не все такие графы изоморфны.
      ]
    ],
    [#diagram({
      node((0, 1),   none, fill: black, radius: 2pt, name: <1>)
      node((0, 1.5), none, fill: black, radius: 2pt, name: <2>)
      node((0, 2),   none, fill: black, radius: 2pt, name: <3>)
      node((0, 2.5), none, fill: black, radius: 2pt, name: <4>)
      node((1, 1),   none, fill: black, radius: 2pt, name: <5>)
      node((1, 1.5), none, fill: black, radius: 2pt, name: <6>)
      node((1, 2),   none, fill: black, radius: 2pt, name: <7>)
      node((1, 2.5), none, fill: black, radius: 2pt, name: <8>)
    
      edge(<1>, <5>, "-")
      edge(<1>, <6>, "-")
      edge(<1>, <7>, "-")
      edge(<2>, <5>, "-")
      edge(<2>, <6>, "-")
      edge(<2>, <8>, "-")
      edge(<3>, <5>, "-")
      edge(<3>, <7>, "-")
      edge(<3>, <8>, "-")
      edge(<4>, <6>, "-")
      edge(<4>, <7>, "-")
      edge(<4>, <8>, "-")
    })],
    [#diagram({
      node((1*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <1>)
      node((2*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <2>)
      node((3*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <3>)
      node((4*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <4>)
      node((5*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <5>)
      node((6*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <6>)
      node((7*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <7>)
      node((8*360deg/8, 0.8), none, fill: black, radius: 2pt, name: <8>)

      edge(<1>, <2>, "-")
      edge(<1>, <8>, "-")
      edge(<1>, <7>, "-")
      edge(<2>, <8>, "-")
      edge(<2>, <3>, "-")
      edge(<3>, <4>, "-")
      edge(<3>, <5>, "-")
      edge(<4>, <5>, "-")
      edge(<4>, <6>, "-")
      edge(<5>, <6>, "-")
      edge(<6>, <7>, "-")
      edge(<7>, <8>, "-")
    })]
  )][
  #grid(
    columns: (3fr, 1fr, 1fr),
    gutter: 10pt,
    [
      #align(left)[
        Контрпример. Во втором случае пути от любой вершины к другой, кроме $u$, проходят через $u$. В первом случае такого нет. Значит не все такие графы изоморфны.
      ]
    ],
    [#diagram({
      node((0, 0),      none, fill: black, radius: 2pt, name: "1")
      node((0.5, 0.5),  none, fill: black, radius: 2pt, name: "2")
      node((-0.5, 0.5), none, fill: black, radius: 2pt, name: "3")
      node((-0.8, 1),   none, fill: black, radius: 2pt, name: "4")
      node((-0.2, 1),   none, fill: black, radius: 2pt, name: "5")
      node((0.2, 1),    none, fill: black, radius: 2pt, name: "6")
      node((0.8, 1),    none, fill: black, radius: 2pt, name: "7")
    
      edge(label("1"), label("2"), "-")
      edge(label("1"), label("3"), "-")
      edge(label("2"), label("6"), "-")
      edge(label("2"), label("7"), "-")
      edge(label("3"), label("4"), "-")
      edge(label("3"), label("5"), "-")
    })],
    [#diagram(debug: 0, {
      node((1*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <1>)
      node((2*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <2>)
      node((3*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <3>)
      node((4*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <4>)
      node((5*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <5>)
      node((6*360deg/6, 0.8), none, fill:black, radius: 2pt, name: <6>)
      node((360deg, 0), move(dy: -13pt, dx: 11pt)[$u$], fill: blue, radius: 2pt, name: <7>)

      edge(<1>, <7>)
      edge(<2>, <7>)
      edge(<3>, <7>)
      edge(<4>, <7>)
      edge(<5>, <7>)
      edge(<6>, <7>)
    })]
  )][
    Это полный граф, т.к. каждая вершина смежна с каждой другой (всего $10$, степень $9$). Все полные графы изоморфны, т.к. нет возможности отличить одну вершину от другой.
  ]
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 5))[]
#solution()[
  Разобъем граф на две доли по четности количества единиц в последовательности. Очевидно что ребра будут только между последовательностями с разными четностями, т.к. изменение одного бита меняет четность строго на $1$. Также каждая последовательность отличается в одной позиции ровно с $n$ другими последовательностями --- для каждой позиции. Значит что $n$-регулярный двудольный граф.

  Количество вершин --- количество последовательностей $2^n$. Т.к. граф $n$-регулярный, то количество ребер
  $ (|V(G)| dot n) / 2 = (2^n dot n) / 2 = 2^(n - 1) dot n $
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 6))[]
#solution()[
  Количество детей у этих $k$ не листьев --- $k dot m$. При этом $k - 1$ вершин тоже чьи-то дети (исключая корень). Значит оставшиеся это листья --- $k dot m - k + 1$.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 7))[]
#solution()[
  Есть два вида деревьев с диаметром $<=3$:
  #align(center)[
    #grid(
      columns: (1fr, 1fr),
      row-gutter: 10pt,
      [*I*],
      [*II*],
      diagram(debug: 0, {
        node((0, 0),  none, fill:black, radius: 2pt, name: <1>)
        node((1, 0),  none, fill:black, radius: 2pt, name: <2>)
        node((-1, 0), none, fill:black, radius: 2pt, name: <3>)
        node((0, 1),  none, fill:black, radius: 2pt, name: <4>)
        node((0, -1), none, fill:black, radius: 2pt, name: <5>)

        edge(<1>, <2>)
        edge(<1>, <3>)
        edge(<1>, <4>)
        edge(<1>, <5>)
      }),
      diagram(debug: 0, {
        node((0, 0),  move(dx: 4pt)[$u$], fill:black, radius: 2pt, name: <1>)
        node((1, 0),  move(dx: 4pt)[$v$], fill:black, radius: 2pt, name: <2>)
        node((-0.5, -0.5),  none, fill:black, radius: 2pt, name: <3>)
        node((-0.5, 0),  none, fill:black, radius: 2pt, name: <4>)
        node((-0.5, 0.5),  none, fill:black, radius: 2pt, name: <5>)
        node((1.5, -0.5),  none, fill:black, radius: 2pt, name: <6>)
        node((1.5, 0),  none, fill:black, radius: 2pt, name: <7>)
        node((1.5, 0.5),  none, fill:black, radius: 2pt, name: <8>)

        edge(<1>, <2>)
        edge(<1>, <3>)
        edge(<1>, <4>)
        edge(<1>, <5>)
        edge(<2>, <6>)
        edge(<2>, <7>)
        edge(<2>, <8>)
      }),
    )
  ]
  В случае *I* все такие графы изоморфны. В случае *II* изоморфны только графы у которые одинаковое количество вершим на какой-то стороне (следовательно и на других тоже), где две стороны это от вершины $u$ и от вершины $v$. Всего вершин на двух сторонах $n - 2$. То есть всег неизоморфных графов типа *II* $floor((n - 2) / 2) = floor(n / 2) - 1$. С учетом одного графа типа *I* неизоморфных графов на $n$ вершинах $floor(n / 2)$.
]
