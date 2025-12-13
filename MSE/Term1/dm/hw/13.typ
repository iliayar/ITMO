#import "common.typ": *

// TODO: Move to common
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge, shapes

#show: doc => hw(12, doc)

#line(length: 100%)
#task(numbering: (..) => numbering("1", 1))[]
#solution()[
  #grid(
    columns: (4fr, 1fr),
    [
      Если граф эйлеровый, то он не обязательно гамильтонов. Любой эйлеров цикл проходит через вершину $u$ два раза. Чтобы обойти все вершины нужно также пройти через $u$ два раза, что не будет гамильтоновым циклом.
    ],
    diagram(debug: 0, {
      node((0, 0),  move(dx: 3pt)[$u$], fill:black, radius: 2pt, name: <1>)
      node((0.5, 0.5),  none, fill:black, radius: 2pt, name: <2>)
      node((-0.5, 0.5),  none, fill:black, radius: 2pt, name: <3>)
      node((-0.5, -0.5),  none, fill:black, radius: 2pt, name: <4>)
      node((0.5, -0.5),  none, fill:black, radius: 2pt, name: <5>)

      edge(<1>, <2>)
      edge(<1>, <3>)
      edge(<3>, <2>)
      edge(<1>, <4>)
      edge(<1>, <5>)
      edge(<4>, <5>)
    }),
  )

  #grid(
    columns: (4fr, 1fr),
    [
      Если граф гамильтонов, то он не обязательно эйлеров.
    ],
    diagram(debug: 0, {
        node((0, -0.5),  none, fill:black, radius: 2pt, name: <0>)
        node((0, 0),  none, fill:black, radius: 2pt, name: <1>)
        node((0.5, 0.5),  none, fill:black, radius: 2pt, name: <2>)
        node((-0.5, 0.5),  none, fill:black, radius: 2pt, name: <3>)

        edge(<1>, <0>)
        edge(<1>, <2>)
        edge(<1>, <3>)
        edge(<3>, <2>)
    })
  )
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 2))[]
#solution()[
  Пусть в эйлеровом графе есть мост. Рассмотрим две компоненты которые он соединяет. Две вершины из двух разных компонент связности должны находитья на эйлеровом цикле. Но т.к. они разных компонент, соединенных мостом, то между ними не может быть цикла. Противоречие.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution()[
  Заметим что граф двудольный:
  #align(center,
    diagram(debug: 0, {
        node((0, 0), none, fill: red.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <0>)
        node((-0.5, -0.5), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <1>)
        node((0.5, -0.5), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <2>)
        node((0.5, 0.5), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <3>)
        node((-0.5, 0.5), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <4>)
        node((0, 1.3), none, fill: red.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <5>)
        node((0, -1.3), none, fill: red.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <6>)
        node((1.3, 0), none, fill: red.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <7>)
        node((-1.3, 0), none, fill: red.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <8>)
        node((2.5, 0), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <9>)
        node((-2.5, 0), none, fill: blue.opacify(-20%), stroke: black + 1pt, radius: 3pt, name: <10>)

        edge(<0>, <1>, stroke: 1pt)
        edge(<0>, <2>, stroke: 1pt)
        edge(<0>, <3>, stroke: 1pt)
        edge(<0>, <4>, stroke: 1pt)
        edge(<1>, <8>, stroke: 1pt)
        edge(<4>, <8>, stroke: 1pt)
        edge(<2>, <7>, stroke: 1pt)
        edge(<3>, <7>, stroke: 1pt)
        edge(<1>, <6>, stroke: 1pt)
        edge(<2>, <6>, stroke: 1pt)
        edge(<3>, <5>, stroke: 1pt)
        edge(<4>, <5>, stroke: 1pt)
        edge(<6>, <10>, stroke: 1pt)
        edge(<5>, <10>, stroke: 1pt)
        edge(<8>, <10>, stroke: 1pt)
        edge(<6>, <9>, stroke: 1pt)
        edge(<5>, <9>, stroke: 1pt)
        edge(<7>, <9>, stroke: 1pt)
    })
  )

  Очевидно что в цикле из нечетного числа вершин должно быть четное число ребер. В двудольном графе никакой путь из четного числа ребер не будет циклом, т.к. его начальная и конечная вершина будут в одной доле. В данном графе нечетное число вершин и он двудольный, значит не существует цикла проходящего через все вершины.
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 3))[]
#solution()[
  Заметим что куб можно представить как граф, а цельные куски проволоки это пути. Также заметим что все вершины имеют степень $3$. При этом если проведем какой-то путь и уберем его из графа, то степень конечных вершин уменьшится на $1$, а остальных на $2$. Значит что если вершина имеет нечетную степень то она должна быть концом хотя бы одно пути. Всего в нашем графе $8$ вершин, значит необходимо как минимум $4$ путя, чтобы степень каждой вершины уменьшилась на $1$. Значит минимальное количество кусков 4, а провести их можно так:
  #align(center,
    diagram(debug: 0, {
        let dx = 0.3
        let dy = -0.2
        let h = 1.5

        node((0, 0 - dy * h), none, fill: black, radius: 2pt, name: <000>)
        node((h, 0 - dy * h), none, fill: black, radius: 2pt, name: <001>)
        node((0 - dx * h, 0 + dy * h), none, fill: black, radius: 2pt, name: <010>)
        node((h - dx * h, 0 + dy * h), none, fill: black, radius: 2pt, name: <011>)

        node((0 - dx * h, h + dy * h), none, fill: black, radius: 2pt, name: <110>)
        node((h - dx * h, h + dy * h), none, fill: black, radius: 2pt, name: <111>)

        node((0, h - dy*h), none, fill: black, radius: 2pt, name: <100>)
        node((h, h - dy*h), none, fill: black, radius: 2pt, name: <101>)

        edge(<100>, <101>, stroke: blue + 2pt)
        edge(<100>, <110>, stroke: blue + 2pt)

        edge(<110>, <111>, stroke: blue + 2pt)
        edge(<101>, <111>, stroke: blue + 2pt)
        edge(<011>, <111>, stroke: blue + 2pt)

        edge(<000>, <001>, stroke: red + 2pt)
        edge(<000>, <010>, stroke: red + 2pt)
        edge(<000>, <100>, stroke: red + 2pt)

        edge(<001>, <011>, stroke: red + 2pt)
        edge(<001>, <101>, stroke: yellow + 2pt)

        edge(<010>, <011>, stroke: red + 2pt)
        edge(<010>, <110>, stroke: green + 2pt)
    })
  )
]

#line(length: 100%)
#task(numbering: (..) => numbering("1", 4))[]
#solution()[
  Построим граф, где ребра будут между теми кто ненавидит друг друга. Заметим что нахождение гамильтонова путя в этом графе будет аналогично разбиению на пары --- возьмем ребра в этом пути через одно, т.к. длина цикла четна ($2n$ вершин), то все будут в паре.
  Осталось показать что в этом графе будет гамильтонов путь. Рассмотрим две несмежные вершины $u$ и $v$ --- т.е. двоих кто не ненавидит друг друга. По условию отсальные $2n - 2$ вершин смежны как минимум с одним из $u$ или $v$. Значит $"deg"(u) + "deg"(v) >= 2 n - 2$. Также известно что есть ненулевое количество вершин, которые смежны и с $u$ и с $v$. Поэтому $"deg"(u) + "deg"(v) >= 2 n - 1$. По теореме Оре это значит что в графе существует гамильтонов путь.
]
