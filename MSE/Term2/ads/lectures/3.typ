#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных. Часть 2],
  title: [Лекция 3],
  date: [24 февраля],
  number: 3,
  program: "ITMO MSE y2025",
  doc
)

= BST

#todo()

#remark[
  $"next"(v)$ --- спускаемся максимально влево
]

== За $cal(O)(1)$

Можем делать `Find` за $cal(O)(1)$ храня мапу из значенй в вершину. Для миинмума/максимуму храним соответственно ссылки на них.

Как делать `Next` за $cal(O)(1)$: храним для каждой вершины `Next` и `Prev`. Обновляем при изменении, получается двусвязный список.

#remark()[
  Нельзя сделать `Add` за $cal(O)(1)$, иначе смогли бы отсортировать массив за $cal(O)(n)$.
]

== AVL

#definition[
  Дерево обладает свойством AVL если для любой вершины, глибуна левого поддерева отличается от глибины правого не более чем на $1$.
]

При добавлении поднимаемся на верх и делаем повороты.

#remark[
  #align(center, diagram(debug: 0, {
    node((0, 0),  move(dy: -10pt)[$y$], fill:black, radius: 2pt, name: <y>)
    node((0.5, 0.7),  [$C$], stroke: black, shape: rect, name: <C>)
    node((-0.5, 0.7),  move(dy: -10pt)[$x$], fill:black, radius: 2pt, name: <x>)
    node((-1, 1.5),  [$A$], stroke: black, shape: rect, name: <A>)
    node((0, 1.5),  [$B$], stroke: black, shape: rect, name: <B>)

    edge(<y>, <x>)
    edge(<y>, <C>)
    edge(<x>, <A>)
    edge(<x>, <B>)
  }))
  Если после добавления в поддерево $B$ получились деревья $h_A = h, h_B = h+1, h_C = h$, то $h_x = h+2$ и нужно сделать поворот. Однако после поворота проблема оставнется.

  Выделать корнеь $z$ в поддереве $B$, и вынести его наверх, $x$ слева, $y$ справа --- *большое вращение*.

  #align(center + horizon, grid(columns:3, gutter: 15pt, diagram(debug: 0, {
    node((0, 0),  move(dy: -10pt)[$z$], fill:black, radius: 2pt, name: <z>)
    node((0.5, 0.7),  [$C$], stroke: black, shape: rect, name: <C>)
    node((-0.5, 0.7),  move(dy: -10pt)[$x$], fill:black, radius: 2pt, name: <x>)
    node((0, 1.3),  move(dx: 10pt, dy: -10pt)[$y$], fill:black, radius: 2pt, name: <y>)
    node((-1, 1.5),  [$A$], stroke: black, shape: rect, name: <A>)
    node((0.5, 2),  [$beta$], stroke: black, shape: rect, name: <beta>)
    node((-0.5, 2),  [$alpha$], stroke: black, shape: rect, name: <alpha>)

    edge(<z>, <x>)
    edge(<z>, <C>)
    edge(<x>, <A>)
    edge(<x>, <y>)
    edge(<y>, <alpha>)
    edge(<y>, <beta>)
  }), [$-->$], diagram(debug: 0, {
    node((0, 0),  move(dx: 10pt, dy: -10pt)[$y$], fill:black, radius: 2pt, name: <y>)
    node((-0.7, 0.7),  move(dy: -10pt)[$x$], fill:black, radius: 2pt, name: <x>)
    node((0.7, 0.7),  move(dy: -10pt, dx: 10pt)[$z$], fill:black, radius: 2pt, name: <z>)
    node((-1.2, 1.5),  [$A$], stroke: black, shape: rect, name: <A>)
    node((-0.3, 1.5),  [$alpha$], stroke: black, shape: rect, name: <alpha>)
    node((1.2, 1.5),  [$C$], stroke: black, shape: rect, name: <C>)
    node((0.3, 1.5),  [$beta$], stroke: black, shape: rect, name: <beta>)

    edge(<y>, <x>)
    edge(<y>, <z>)
    edge(<x>, <A>)
    edge(<x>, <alpha>)
    edge(<z>, <beta>)
    edge(<z>, <C>)
  })))
]

#theorem[
  Всегда делаем не больше одного вращения
]

#remark[
  При удалении можем помечать вершину как удаленную и что-то делать потом с ней #todo()
]

= Хеш-Таблицы

Заводим массив массивов и маппим индексы в нем $i -> i mod N$, где $N$ размер массива.

#remark[
  Вместо фиксированного $N$ берем рандом от $N$ до $2N$. Тогда вероятность коллизии $i mod N' != j mod N'$. $i - j divides N'$ с вероятностью(?) $log$.

  #todo()
]

== Открытая адресация

#remark[
  При удалении помечаем как "удаленный"
]
