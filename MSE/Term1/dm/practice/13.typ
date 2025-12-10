#import "/other/typst/practice_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *


#show: doc => practice(
  subj: [Дискретная математика],
  title: [Практика 13],
  date: [10 декабря],
  number: 13,
  doc
)

#task(numbering: (..) => numbering("1", 6))[]
#solution()[
  Вершины --- команды, ребра --- команды, которые не играли между собой. $|V(G)| = 2n$. $forall v med "deg"(v) = n$ --- всего $2n - 1$ сосед, с $n - 1$ уже сыграли, $==>$ не играли с $n$. По теореме Дирака в $G$ существует гамильтонов цикл (он имеет длины $2n$). В этом цикле два паросочетания.
]
