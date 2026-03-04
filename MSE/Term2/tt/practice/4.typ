#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 4],
  date: [4 марта],
  number: 4,
  author: "Ярошевский Илья",
  doc
)

#task(numbering: (..) => numbering("1", 1))[ $ (alpha -> beta -> gamma) -> (alpha -> beta) -> alpha -> gamma $ ]
#solution[
  #align(center, diagram(
    node-stroke: 1pt,
    node-inset: 5pt,
    node-shape: "rect",
    node((0, 0), $(alpha -> beta -> gamma) -> (alpha -> beta) -> alpha -> gamma$),
    edge((0, 0), (3, 0), "->", $lambda f^(alpha -> beta -> gamma) med g^(alpha->beta) med x^alpha.$),
    node((3, 0), $gamma$),
    edge((3, 0), (4, 0), "->", $f$),
    edge((3, 0), (4, 1), "->", $f$),
    node((4, 0), $alpha$),
    node((4, 1), $beta$),
    edge((4, 1), (4, 0), "->", $g$),
    node((4, -1), $x$, stroke: 0pt),
    edge((4, 0), (4, -1), "->"),
  ))
]

#task(numbering: (..) => numbering("1", 2))[ $ (alpha -> beta) -> (beta -> alpha) -> (alpha -> gamma) -> beta -> gamma  $ ]
#solution[
  #align(center, diagram(
    node-stroke: 1pt,
    node-inset: 5pt,
    node-shape: "rect",
    node((0, 0), $(alpha -> beta) -> (beta -> alpha) -> (alpha -> gamma) -> beta -> gamma$),
    edge((0, 0), (3, 0), "->", $lambda f^(alpha -> beta) med g^(beta -> alpha) med h^(alpha -> gamma) med x^beta.$),
    node((3, 0), $gamma$),
    edge((3, 0), (3, 1), "->", $h$),
    node((3, 1), $alpha$),
    edge((3, 1), (2, 1), "->", $g$),
    node((2, 1), $beta$),
    node((1, 1), $x$, stroke: 0pt),
    edge((2, 1), (1, 1), "->"),
    edge((2, 1), (2, 1.4), (3, 1.4), (3, 1), "->", $f$, label-side: right),
  ))
]

#task(numbering: (..) => numbering("1", 3))[ $ ((((alpha -> alpha) -> alpha) -> alpha )-> alpha) -> alpha  $ ]
#solution[

  #align(center, diagram(
    node-stroke: 1pt,
    node-inset: 5pt,
    node-shape: "rect",
    node((0, 0), $((((alpha -> alpha) -> alpha) -> alpha) -> alpha) -> alpha$),
    edge((0, 0), (3, 0), "->", $lambda f^((((alpha -> alpha) -> alpha) -> alpha) -> alpha).$),
    node((3, 0), $alpha$),
    edge((3, 0), (4, 0), "->", $f$),
    node((4, 0), $((alpha -> alpha) -> alpha) -> alpha$),
    edge((4, 0), (6, 0), "->", $lambda g^((alpha -> alpha) -> alpha).$),
    node((6, 0), $alpha$),
    edge((6, 0), (6, 0.4), (4, 0.4), (4, 0), "->", $f$, label-side: left),
    edge((6, 0), (6, -1), "->", $g$),
    node((6, -1), $alpha -> alpha$),
    edge((6, -1), (5, -1), "->", $lambda x^alpha$),
    node((5, -1), $alpha$),
    node((4, -1), $x$, stroke: 0pt),
    edge((5, -1), (5, -1.6), (6, -1.6), (6, -1), "->", $g$),
    edge((5, -1), (4, -1), "->"),
    edge((5, -1), (5, -0.6), (4, -0.6), (4, 0), "->", $f$, label-side: center),
  ))
]
