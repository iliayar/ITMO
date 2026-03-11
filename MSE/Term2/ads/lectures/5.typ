#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Алгоритмы и структуры данных. Часть 2],
  title: [Лекция 5],
  date: [10 марта],
  number: 5,
  program: "ITMO MSE y2025",
  doc
)

= Дерево версий
Для оффлайна. Строим граф с изменениями, проходим по графу, меняем, например `a[i] = x`. Когда приходим в вершину где запрос на получение --- уже есть нужная версия. Когда выходим из dfs'а откатываем `a[i] = y`.

= Splay. Время работы
Возьмем потенциалы $phi = sum_v log "size"[v]$. $a_i = t_i + Delta phi$. Пусть $R(v) = log "size"[v]$.
#theorem[
  $Delta phi_i <= 3 (R(v') - R(v)) - 2$.
]
#lemma[
  Если $x, y > 0$ и $x + y = 1$, то $log x + log y <= -2$
]
#proof[
  - zig-zig. Вершины сверху вниз $z, y, x$. Соответственно $x', y', z'$ --- после поворота. Тогда
    $ Delta phi = R(x') + R(y') + R(z') - R(x) - R(y) - R(z)  $
    #todo()
]
