#import "common.typ": *

#show: doc => hw(doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 1, 1))[]
#solution[
  Пока не видели 0 словно подходит S, как только увидели 0 Z, то встреченная единица будет означать что слово не подходит D. Строки где сначала 1 потом 0

  #align(center, automaton(
    (
      S: (S: 1, Z: 0),
      Z: (Z: 0, D: 1),
      D: (D: (0, 1)),
    ),
    final: ("S", "Z"),
  ))
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 1, 2))[]
#solution[
  Считаем количество a и b --- сотояния $a_i b_j$. Если a превисило $2$ попадаем в терминальную вершину $D$. Вершины $a_i b_3$ где $i <= 2$ допускающие.

  #align(center, diagram(
    node-stroke: 1pt,
    spacing: 2em,
    node-shape: "circle",
    node((0, 0), $S$),
    edge((-1, 0), "r", "->"),
    node((1, 1), $a_1 b_0$),
    edge((0, 0), (1, 1), "->", `a`, label-side: right),
    node((1, 0), $a_0 b_1$),
    edge((0, 0), (1, 0), "->", `b`),
    node((2, 0), $a_0 b_2$),
    edge((1, 0), (2, 0), "->", `b`),
    node((3, 0), $a_0 b_3$, extrude: (-2, 0)),
    edge((2, 0), (3, 0), "->", `b`),
    edge((3, 0), (3, 0), "->", `b`, bend: 130deg),

    node((2, 1), $a_1 b_1$),
    edge((1, 1), (2, 1), "->", `b`),
    edge((1, 0), (2, 1), "->", `a`),
    node((3, 1), $a_1 b_2$),
    edge((2, 1), (3, 1), "->", `b`),
    edge((2, 0), (3, 1), "->", `a`),
    node((4, 1), $a_1 b_3$, extrude: (-2, 0)),
    edge((3, 1), (4, 1), "->", `b`),
    edge((3, 0), (4, 1), "->", `a`),
    edge((4, 1), (4, 1), "->", `b`, bend: 130deg),

    node((2, 2), $a_2 b_0$),
    edge((1, 1), (2, 2), "->", `a`),
    node((3, 2), $a_2 b_1$),
    edge((2, 2), (3, 2), "->", `b`),
    edge((2, 1), (3, 2), "->", `a`),
    node((4, 2), $a_2 b_2$),
    edge((3, 2), (4, 2), "->", `b`),
    edge((3, 1), (4, 2), "->", `a`),
    node((5, 2), $a_2 b_3$, extrude: (-2, 0)),
    edge((4, 2), (5, 2), "->", `b`),
    edge((4, 1), (5, 2), "->", `a`),
    edge((5, 2), (5, 2), "->", `b`, bend: 130deg),

    node((4, 4), $D$),
    edge((5, 2), (4, 4), "->", `a`, label-side: center),
    edge((4, 2), (4, 4), "->", `a`, label-side: center),
    edge((3, 2), (4, 4), "->", `a`, label-side: center),
    edge((2, 2), (4, 4), "->", `a`, label-side: center),
    edge((4, 4), (4, 4), "->", [`b`, `a`], bend: -130deg),
  ))
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 1, 3))[]
#solution[
  В состояниях храним остаток от деления на $3$ суммы чисел и последнее число. Число делится на $15$ если заканчивается на $0$ или $5$ и остаток от деления на $3$ суммы равен $0$. Помечаем соответствующие состояния как допускающие:
  #align(center, diagram(
    node-stroke: 1pt,
    spacing: 2em,
    node-shape: "circle",
    node((0, 0), $S$),
    edge((-1, 0), "r", "->"),
    node((1, 0), $n mod 3, n$),
    edge((0, 0), (1, 0), $n$, "->"),

    edge((1, 0), (2, 0), "->", dash: "dashed"),
    node((2, 0), $n, k$),
    node((3, 0), $n + d mod 3, d$),
    edge((2, 0), (3, 0), $d$, "->"),

    edge((3, 0), (4, -1), "->", dash: "dashed"),
    edge((3, 0), (4, 1), "->", dash: "dashed"),
    node((4, -1), $0, 0$, extrude: (-2, 0)),
    node((4, 1), $0, 5$, extrude: (-2, 0)),
  ))
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 1, 4))[]
#solution[
  Аналогично поддерживаем остаток от деления на $5$. Если текущее число $x$, то читая бит $b$, видимое число становится равно $2 dot x + b$. Тогда остаток от деления меняется так $x' mod 5 = (2 dot x + b) mod 5 = 2 dot x mod 5 + b mod 5$
  #align(center, diagram(
    node-stroke: 1pt,
    spacing: 2em,
    node-shape: "circle",
    edge((-1, 0), "r", "->"),
    node((0, 0), $S$),
    node((1, -1), $0$, extrude: (-2, 0)),
    node((1, 1), $1$),
    node((2, 1), $3$),
    node((2, -1), $2$),
    node((3, 0), $4$),

    edge((0, 0), (1, -1), $0$, "->"),
    edge((0, 0), (1, 1), $1$, "->", label-side: right),

    edge((1, -1), (1, 1), $1$, "->", label-side: center),
    edge((1, -1), (1, -1), $0$, "->", bend: 130deg),

    edge((1, 1), (2, 1), $1$, "->"),
    edge((1, 1), (2, -1), $0$, "->", label-side: center),

    edge((2, 1), (1, 1), $0$, "->", bend: 30deg),
    edge((2, 1), (2, -1), $1$, "->", label-side: center),

    edge((2, -1), (1, -1), $1$, "->"),
    edge((2, -1), (3, 0), $0$, "->"),

    edge((3, 0), (3, 0), $1$, "->", bend: 130deg, loop-angle: 1800deg),
    edge((3, 0), (2, 1), $0$, "->", label-side: left),
  ))
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution[
  Заметим что НКА принимает слова с подпоследовательностью 1, 0 или 1, 0

  #align(center, diagram(
    node-stroke: 1pt,
    spacing: 2em,
    node-shape: "circle",
    edge((-1, 0), "r", "->"),
    node((0, 0), $epsilon$),
    node((1, 0), `1`),
    node((2, -1), `10`),
    node((2, 1), `11`),
    node((3, 0), `1{0,1}0`, extrude: (-2, 0)),

    edge((0, 0), (0, 0), `0`, "->", bend: 130deg),
    edge((0, 0), (1, 0), `1`, "->"),

    edge((1, 0), (2, -1), `0`, "->", label-side: right),
    edge((1, 0), (2, 1), `1`, "->"),

    edge((2, -1), (3, 0), `0`, "->"),
    edge((2, -1), (1, 0), `1`, "->", bend: -30deg),

    edge((2, 1), (3, 0), `0`, "->"),
    edge((2, 1), (2, 1), `1`, "->", bend: -130deg),

    edge((3, 0), (3, 0), [`0`, `1`], "->", bend: 120deg),
  ))
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 3, 1))[]
#solution[
  #block(breakable: false)[#align(center, grid(
    columns: 2,
    column-gutter: 5em,
    [Автомат для языка из слов без подстроки `111`], [Дополнение для него],
    diagram(
      node-stroke: 1pt,
      spacing: 2em,
      node-shape: "circle",
      edge((-1, 0), "r", "->"),
      node((0, 0), $S$, extrude: (-2, 0)),
      node((1, 0), `1`, extrude: (-2, 0)),
      node((2, 0), `11`, extrude: (-2, 0)),
      node((3, 0), `111`),

      edge((0,0), (0, 0), `0`, "->", bend: -130deg),
      edge((0, 0), (1, 0), `1`, "->"),
      edge((1, 0), (2, 0), `1`, "->"),
      edge((2, 0), (3, 0), `1`, "->"),
      edge((3, 0), (3, 0), [`1`, `0`], "->", bend: -130deg),

      edge((1, 0), (0, 0), `0`, "->", bend: -60deg),
      edge((2, 0), (0, 0), `0`, "->", bend: 40deg),
    ),
    diagram(
      node-stroke: 1pt,
      spacing: 2em,
      node-shape: "circle",
      edge((-1, 0), "r", "->"),
      node((0, 0), $S$),
      node((1, 0), `1`),
      node((2, 0), `11`),
      node((3, 0), `111`, extrude: (-2, 0)),

      edge((0,0), (0, 0), `0`, "->", bend: -130deg),
      edge((0, 0), (1, 0), `1`, "->"),
      edge((1, 0), (2, 0), `1`, "->"),
      edge((2, 0), (3, 0), `1`, "->"),
      edge((3, 0), (3, 0), [`1`, `0`], "->", bend: -130deg),

      edge((1, 0), (0, 0), `0`, "->", bend: -60deg),
      edge((2, 0), (0, 0), `0`, "->", bend: 40deg),
    )
  ))]
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 3, 2))[]
#solution[
  #align(center + horizon, grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: (1em,),
    [$L_1$], [$L_2$],
    {
      let odd = (1, 0)
      let even = (0, 0)
      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",
        edge((-1, 0), "r", "->"),
        node(even, [even], extrude: (-2, 0)),
        node(odd, [odd]),

        edge(odd, odd, `0`, "->", bend: 130deg),
        edge(even, even, `0`, "->", bend: 130deg),
        edge(odd, even, `1`, "->", bend: 30deg),
        edge(even, odd, `1`, "->", bend: 30deg),
      )
    },
    {
      let empty = (0, 0)
      let z = (1, 0)
      let zo = (2, 0)
      let zoz = (3, 0)
      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",
        edge((-1, 0), "r", "->"),
        node(empty, [$epsilon$]),
        node(z, [`0`]),
        node(zo, [`01`]),
        node(zoz, [`010`], extrude: (-2, 0)),

        edge(empty, z, `0`, "->"),
        edge(empty, empty, `1`, "->", bend: -130deg),
        edge(z, zo, `1`, "->"),
        edge(z, z, `0`, "->", bend: -130deg),
        edge(zo, zoz, `0`, "->"),
        edge(zo, empty, `1`, "->", bend: -50deg),
        edge(zoz, zoz, [`1`, `0`], "->", bend: -130deg),
      )
    },
  ))
  #align(center + horizon, [
    $L_1 union L_2$ (но это НКА) \
    #{
      let S = (-1, 0)

      let empty = (0, -2)
      let z = (1, -2)
      let zo = (2, -2)
      let zoz = (3, -2)

      let odd = (1, 2)
      let even = (0, 2)

      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",

        edge((-2, 0), "r", "->"),
        node(S, [$S$]),
        edge(S, empty, $epsilon$, "->", bend: 20deg),
        edge(S, even, $epsilon$, "->", bend: -20deg),

        node(empty, [$epsilon$]),
        node(z, [`0`]),
        node(zo, [`01`]),
        node(zoz, [`010`], extrude: (-2, 0)),

        edge(empty, z, `0`, "->"),
        edge(empty, empty, `1`, "->", bend: -130deg),
        edge(z, zo, `1`, "->"),
        edge(z, z, `0`, "->", bend: -130deg),
        edge(zo, zoz, `0`, "->"),
        edge(zo, empty, `1`, "->", bend: -50deg),
        edge(zoz, zoz, [`1`, `0`], "->", bend: -130deg),

        node(even, [even], extrude: (-2, 0)),
        node(odd, [odd]),

        edge(odd, odd, `0`, "->", bend: 130deg),
        edge(even, even, `0`, "->", bend: 130deg),
        edge(odd, even, `1`, "->", bend: 30deg),
        edge(even, odd, `1`, "->", bend: 30deg),
      )
    },
  ])
]

#line(length: 100%)
#task(numbering: (..) => numbering("1.1", 3, 3))[]
#solution[
  Предположу что имелось ввиду вместо `a` --- `0`, а вместо `b` --- `1`.
  #align(center + horizon, grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: (1em,),
    [$L_1$], [$L_2$],
    {
      let odd = (1, 0)
      let even = (0, 0)
      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",
        edge((-1, 0), "r", "->"),
        node(even, [even]),
        node(odd, [odd], extrude: (-2, 0)),

        edge(odd, odd, `0`, "->", bend: 130deg),
        edge(even, even, `0`, "->", bend: 130deg),
        edge(odd, even, `1`, "->", bend: 30deg),
        edge(even, odd, `1`, "->", bend: 30deg),
      )
    },
    {
      let empty = (0, 0)
      let z = (1, 0)
      let zz = (2, 0)
      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",
        edge((-1, 0), "r", "->"),
        node(empty, [$epsilon$]),
        node(z, [`0`]),
        node(zz, [`00`], extrude: (-2, 0)),

        edge(empty, empty, `1`, "->", bend: -130deg),
        edge(empty, z, `0`, "->"),
        edge(z, zz, `0`, "->"),
        edge(z, empty, `1`, "->", bend: -60deg),
        edge(zz, empty, `1`, "->", bend: 30deg),
        edge(zz, zz, `0`, "->", bend: 130deg),
      )
    },
  ))
  #align(center + horizon, [
    $L_1 dot L_2$ \
    #{
      let empty = (2, 0)
      let z = (3, 0)
      let zz = (4, 0)

      let odd = (1, 0)
      let even = (0, 0)

      diagram(
        node-stroke: 1pt,
        spacing: 2em,
        node-shape: "circle",
        edge((-1, 0), "r", "->"),
        node(empty, [$epsilon$]),
        node(z, [`0`]),
        node(zz, [`00`], extrude: (-2, 0)),

        edge(empty, empty, `1`, "->", bend: -130deg),
        edge(empty, z, `0`, "->"),
        edge(z, zz, `0`, "->"),
        edge(z, empty, `1`, "->", bend: -60deg),
        edge(zz, empty, `1`, "->", bend: 30deg),
        edge(zz, zz, `0`, "->", bend: 130deg),

        node(even, [even]),
        node(odd, [odd]),

        edge(odd, odd, `0`, "->", bend: 130deg),
        edge(even, even, `0`, "->", bend: 130deg),
        edge(odd, even, `1`, "->", bend: 30deg),
        edge(even, odd, `1`, "->", bend: 30deg),

        edge(odd, empty, $epsilon$, "->"),
      )
    },
  ])
]
