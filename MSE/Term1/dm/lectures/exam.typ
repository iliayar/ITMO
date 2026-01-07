#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Вопросы к экзамену],
  date: [14 января],
  number: 0,
  doc
)

= Вопросы
== Методы математического доказательства. Метод математической индукции. Аксиомы индукции. Примеры.
1. База $n = 0$, ИП $k mapsto k + 1$
2. База $n = 0$, ИР $1, dots, k mapsto k + 1$
  #example()[Сумма углов в прямоугольнике]
3. База $n = 0, n = 1, n = 2$, ИП $k mapsto k + 3$.
  #example()[Докажите, что квадрат можно разрезать на $n$ квадратов (не обязательно одинаковых) для любого $n \ge 6$]
4. База $n = 1$, ИП $2^k mapsto 2^(k + 1), k mapsto k - 1$.

Аксиома индукции (Пеано): $P(0) and forall n med (P(n) ==> P(n + 1)) ==> forall n in NN med P(n)$ #fixme()

== Методы математического доказательства. Принцип Дирихле. Примеры применения в комбинаторике.
#lemma()[
  Есть $n$ клеток и $m$ ($m > (k - 1) dot n$) кроликов (голубей), тогда $exists$ клетка, в которой находятся $>= k$ кролика.
]
#proof()[
  Пусть не так. В каждой клетке $<= k - 1$ кролик. Тогда всего $<= n dot (k - 1)$ кроликов. Противоречие.
]
#example()[
  Макс. кол-во королей, которые можно разместить на доске $8 times 8$, так чтобы они не били друг друга.
]
#solution()[
  Ни в каком квадрате $2 times 2$ не может стоять два короля. По принципу Дирихле верхняя граница --- $(8 / 2)^2 = 16$
]
== #todo() Методы математического доказательства. Остальные методы с примерами.
1. Примеры и контрпримеры
2. Прямое доказательство
3. Обратное доказательство
4. Оценка + пример
   #example()[
     Какое максимальное количество ферзей можно расставить на шахматной доске, так чтобы они не били друг друга? Больше 8 нельзя, т.к. в каждом столбце максимум 1 (оценка). Покажем как расставить 8 (пример).
   ]
5. Оценка с двух сторон
6. Комбинаторный метод
== Комбинаторика. Мощности множеств. Мощность объединения и пересечения множеств. Формула включений-исключений.
- $|A| <= |A union B|$
- $|A| >= |A inter B|$
#fixme(note: "В лекциях нет?")

#theorem("Формула включения исключений")[
  $A, B subset X$.
  $ |overline(A union B)| = |X| - |A union B| = |X| - |A| - |B| + |A inter B| $
]

#remark()[
  Обобщается
  $ |overline(A union B union C)| = |X| - |A| - |B| - |C| + |A inter B| + |B inter C| + |C inter A| - |A inter B inter C| $
]

== Комбинаторика. Правила суммы и произведения.
#remark()[
  Правило суммы: $A , B : A inter B = emptyset$, $|A union B| = |A| + |B|$
]
#remark()[$|X times Y| = |X| dot |Y|$]
== Комбинаторика. Размещения с повторениями и без.
#theorem("Размещения с повторениями")[
  Количество способов выбрать $k$ элементов и $n$ элементного множества с учетом того что элементы могут повторяться и важен порядок выбора
  $ n^k $
]
#theorem("Размещения без повторений")[
  Количество способов выбрать $k$ элементов и $n$ элментного множества с учетом того что элементы не могут повторяться, но важен порядок выбора
  $ n dot (n - 1) dot (n - 2) dot ... dot (n - k + 1) = frac(n!, (n - k)!) = A^k_n = n_((k)) $
]
== Комбинаторика. Перестановки с повторениями и без.
#theorem("Перестановки без повторений")[
  Количество спобосбов упорядочить $n$-элементное множество
  $ n! = P(n) $
]
#remark()[$ P(n) = A^n_n $]
#definition()[
  Пусть имеется $k_1$ элементов *I* типа, $k_2$ элементов *II* типа, #math.dots, $k_l$ элементов $l$ типа. Количество различных перестановок этих $n$ элементов называется *перестановки с повторениями*
]
#symb()[
  $ binom(n, k_1, k_2, dots, k_l) = P(n; k_1, k_2, dots, k_l) $
]
#statement()[
  $ binom(n, k_1, k_2, dots, k_l) = frac(n!, k_1! k_2! dots k_l!) $
]
#proof("На примере")[
  Возьмем $X_1, X_2, X_3, Y_1, Y_2, Z_1, Z_2$. Количество перестановок $n!$. Теперь сотрем индексы у $X$, перестали различать некоторые перестановки. Общее количество уменьшилось в $k_X !$ раз.
]
== Комбинаторика. Сочетания с повторениями и без.
#theorem("Сочетания без повторений")[
  Количество способов выбрать $k$ элементов из $n$-элементного множества без учета порядка, с учетом того что элементы не могут повторяться
  $ C^k_n = binom(n, k) = frac(n!, k! dot (n - k)!) $
]
#example()[Количество $k$-элементных подмножеств $n$-элементного множества]

Количество способов выбрать $k$ элементов из $n$-элементного множества, с учетом того что порядок не важен и элементы могут повторяться. Количество $k$-мультимножеств над $n$ элементным множеством

#symb()[
  $ multiset(n, k) = overline(C_n^k) $
]
#statement()[
  $ multiset(n, k) = binom(n + k - 1, k) $
]
#proof()[
  Пусть имеется $n$ различных ящиков, в которые распределяем $k$ одинаковых шариков. Сколько способов это сделать. Мультимножество над ящиками задает раскладку шариков по ящикам:
  $ multiset(n, k) $

  Расставим $k - 1$ перегородок между шариками --- это также задает раскладку шариков по ящикам. Шарики --- $0$, перегородки --- $1$. Составляем бинарную строку длины $n + k - 1$ в которых $k$ нулей:
  $ binom(n + k - 1, k) $
]
#remark()[
  $ multiset(n, k) = binom(n + k - 1, k) = frac((n + k - 1)!, k! (n - 1)!) = frac(n dot (n + 1) dot dots dot (n + k - 1), k!) = frac(n^((k)), k!) $
  , где $n^((k))$ --- возрастающая факториальная степень
]
== #todo() Комбинаторика. Биномиальные коэффициенты. Явные и рекуррентные формулы. Свойства.
#lemma()[
  Бином Ньютона
  $ (x + y)^n = sum_(k = 0)^n binom(n, k) x^k y^(n - k) $
  Коэффициент --- сколько способов тыкнуть в $x$ $k$ раз
]
#corollary_lemma()[
  $ x = y = 1 quad sum_(k = 0)^n = 2^n $
  Количество подмножеств
]
#corollary_lemma()[
  $ x = -1 thick y = 1 quad 0 = sum_(k = 0)^n binom(n, k) (-1)^k quad n != 0 $
]
#example()[
    Граничное условие
    $ binom(n, k) = 0, quad k > n $
]

#example()[
    Начальное условие
    $ binom(n, 0) = 1 $
]

#example()[
  $ binom(n, k) = binom(n - 1, k) + binom(n - 1,k - 1) $
  Придумаем два способа решения одной и той же задачи. Формулы для решений будут эквивалентны, т.к.
  решаем одну и ту же задачу
]
#proof()[
  #task()[
      В магазине $n$ различных шоколадок, хотим купить $k$ из них. Сколько способов?
  ]
  #solution()[
    По определению $binom(n, k)$
  ]
  #solution()[
    Разобьем на два не пересекающихся подмножества. Пусть есть одна особенная шоколадка. Тогда два случая: купили эту особенную или нет.
    - Осталось добрать $k - 1$ из оставшихся $n$ --- $binom(n - 1, k - 1)$
    - $binom(n - 1, k)$
  ]
]

== #todo() Комбинаторика. Различные интерпретации биномиальных коэффициентов. Тождество Вандермонда.
#example()[
  Тождество Вандермонда
  $ sum_(k = 0)^l binom(n, k) binom(m, l - k) = binom(n + m, l) $
]
#proof()[
  #task()[
    Есть $n$ мальчиков и $m$ девочек, сколько способов выбрать команду размера $l$.
  ]
  #solution()[
    Тривиально правая часть тождества
  ]
  #solution()[
    Разобьем по количеству мальчиков в команде (от $0$ до $n$).
    $ sum_(k = 0)^l binom(n, k) binom(m, l - k) $
  ]
]
== Комбинаторика. Количество отображений. Инъекции и биекции.
#definition()[
  Отображением $delta$ из $X$ в $Y$ называется некое правило соответствия $forall x in X quad exists! y in Y : f(x) = y$
]

#remark()[
  $|X| = n, |Y| = m$ количество отображений $m^n$.
]

#definition()[
  Отображение называется *инъективным*, если $f(x_1) = f(x_2) ==> x_1 = x_2$
]
#remark()[
  Всего инъективных отображений $A_m^n$
]
#remark()[
  Если $n > m$, то инъекций не существует (принцип Дирихле) 
]

#definition()[
  Отображение называется *биективным*, если $forall y in Y, exists ! x in X : f(x) = y$ (инъекция + сюръекция)
]
#remark()[Всего биекций $n!$]

== Комбинаторика. Формула обращения.
#theorem()[
$ f_k = sum^k_(i = 0) binom(k, i) g_i <==> g_k = sum^k_(i = 0) (-1)^(k - i)binom(k, i) f_i $, где $f_k$, $g_k$ --- числовые последовательности
]
#proof()[
  1. $quote.double==>quote.double$ Рассмотрим 
    $ 
      sum_(i = 0)^k (-1)^(k - i) binom(k, i) f_i = sum_(i = 0)^k (-1)^(k - i) binom(k, i) sum_(j = 0)^i binom(i, j) g_j = sum_(i = 0)^k sum_(j = 0)^i (-1)^(k - i) binom(k, i) binom(i, j) g_i =  \
      = sum_(i = 0)^k sum_(j = 0)^i (-1)^(k - i) binom(k, j) binom(k - j, i - j) g_j = sum_(j = 0)^k sum_(i = j)^k (-1)^(k - i) binom(k, j) binom(k - j, i - j) g_j = \
      = sum_(j = 0)^k binom(k, j) g_j sum_(i = j)^k (-1)^(k - i) binom(k - j, i - j) = sum_(j = 0)^k binom(k, j) g_j sum_(l = 0)^(k - j) (-1)^(k - j - l) binom(k - j, l) = #h(5em)#text(gray)[$[l = i - j]$] \
     = sum_(j = 0)^k binom(k, j) g_j sum_(l = 0)^m (-1)^(m - l) binom(m, k) dot 1^k = binom(k, k) g_j = g_j #h(5em)#text(gray)[$[m = k - j]$]
    $
]
== Комбинаторика. Количество сюръекций. Числа Стирлинга второго рода.
#definition()[
  *Числа Стирлинга #numbering("I", 2) рода* $S(n, k)$ --- количество способов разбить $n$ элементное множество на $k$ непустых подмножеств
]
#symb()[ $stirling(n, k)$ ]

#remark()[
    $ S(n, k) = sum_(i = 0)^(n - 1) S(n - i, k - 1) dot binom(n - 1, i) $
]

#remark()[
    $ S(n, k) = S(n - 1, k - 1) + S(n - 1, k) dot k $
]

#definition()[
  Отображение называется *сюръективным*, если $forall y in Y , exists x : f(x) = y$
]

#definition()[
  Всего сюръекций $hat(S)(n, m)$
]
#remark()[
  $k! dot S(n, k) = hat(S)(n, k)$
]
#theorem()[
    $ hat(S)(n, k) = sum_(i = 0)^k (-1)^(k - i) binom(k, i) i^n $
]

== Комбинаторика. Числа Белла.

#definition()[
  *Числами Белла*  называется количество способов разбить $n$-элементное множество на подмножества
]
#symb()[$B(n)$]
#remark()[
    $ B(n) = sum_(k = 1)^n S(n, k) $
]

== Комбинаторика. Урновая схема. Схема шаров и ящиков.
#remark()[
  Урновая схема. Есть $n$ _различимых_ шариков в урне, выбираем $k$ из них.
  #table(
    columns: 3,
    align: center,
    stroke: none,
    [], table.vline(), [Важен порядок], table.vline(), [Не важен порядок],
    table.hline(),
    [Шары не возвращаются], [Размещения без повторений \ $A^k_n$], [$binom(n, k)$],
    table.hline(),
    [Шары возвращаются], [$n^k$], [$multiset(n, k)$],
  )
]

#remark()[
  Схема шаров и ящиков. Есть $n$ различимых ящиков и $k$ шаров, хотим разложить шары по ящикам
  #table(
    columns: 3,
    align: center,
    stroke: none,
    [], table.vline(), [Шары различимы], table.vline(), [Шары не различимы],
    table.hline(),
    [Максимум 1 шар в ящик], [$A_n^k$], [$binom(n, k)$],
    table.hline(),
    [Без ограничений], [$n^k$], [#box($multiset(n, k)$)],
  )
]

$n$ ящиков, $k$ шариков

#align(center, table(
  columns: 4,
  stroke: none,
  align: center,
  gutter: 0.5em,
  [], table.vline(), [ящики \\ шарики], table.vline(), [различимы], table.vline(), [неразличимы],
  table.hline(),
  table.cell(rowspan: 3)[#rotate(-90deg, reflow: true)[различимы]] /* rotate it 90*/, [$<= 1$ шарика в ящик], [$A^k_n$], [$binom(n, k)$],
  [без ограничений], [$n^k$], [$multiset(n, k)$],
  [нет пустых ящиков], [$hat(S)(k, n)$], [$multiset(n, k - n)$],
  table.hline(),
  table.cell(rowspan: 3)[#rotate(-90deg, reflow: true)[неразличимы]], [$<= 1$ шарика в ящик], [$cases(1\, k <= n, 0\, k > n)$], [$cases(1\, k <= n, 0\, k > n)$],
  [без ограничений], [$sum_(i = 1)^n S(k, i)$], [$sum_(i = 1)^n p_i(k)$],
  [нет пустых ящиков], [$S(k, n)$], [$p_n(k)$]
))

#definition()[
  $p_k(n)$ --- количество способов разбить числа $n$  на $k$ натуральных слагаемых
  $ cases(n = n_1 + n_2 + dots + n_l, 1 <= n_1 <= n_2 <= dots <= n_k) $
]
#example()[
  $
    p_3(6) = 3 \
    1 + 1 + 4 \
    1 + 2 + 3 \
    2 + 2 + 2
  $
]
== Рекуррентные соотношения. Характеристические уравнения. Однородные рекуррентные соотношения без кратных и комплексно-сопряженных корней.
#definition()[
  $a_(n + m) = f_n (a_(n + m - 1), a_(n + m - 2), dots, a_n)$ --- *рекуррентное соотношение* (рекуррента) $m$-того порядка, где $a_0, a_1, dots, a_(m - 1)$ --- начальные условия

  Будем рассматривать рекуррентные соотношения вида $a_(n + m) = b_1(n) dot a_(n + m - 1) - b_2(n) dot a_(n + m - 2) + dots + b_,(n) dot a_n + u(n)$ --- линейное рекуррентное соотношение. $a_(n + m) = b_1 dot a_(n + m - 1) + b_2 dot a_(n + m - 2) + dots + b_m a_n + u(n)$ --- линейное рекуррентное соотношение с постоянными коэффициентами.
  
  Если $u(n) equiv 0$, тогда линейное рекуррентное соотношение называется однородным.
]

$a_(n + 2) = b dot a_(n + 1) + c dot a_n$. Попробуем найти ответ в виде $a_n = lambda^n$.
$
  lambda^(n + 2) = b dot lambda^(n + 1) + c dot lambda^n \
  lambda^2 - b lambda - c = 0 #text[ --- характеристическое уравнение]
$

#remark()[
  $lambda_1 != lambda_2$ --- вещественные корни характеристического уравнения
  $
    a_n = c_1 lambda_1^n + c_2 lambda_2^n #text[ --- общее решение] \
    c_1 lambda_1^(n + 2) + c_2 lambda_2^(n + 2) = b(c_1 lambda_1^(n + 1) + c_2 lambda_2^(n + 1)) + c(c_1 lambda_1^n + c_2 lambda_2^n) \
    c_1 lambda_1^n (lambda_1^2 - b lambda_1 - c) + c_2 lambda_2^n (lambda_2^2 - b lambda_2 - c) = 0
  $
] <first-case-roots>

#example()[
  Количество способов разбить полоску длины $n$, ширины $2$ доминошками $2 times 1$.
  $ a_(n + 2) = a_(n + 1) + a_n $
  Характеристическое уравнение $lambda^2 - lambda - 1 = 0$, где $lambda = frac(1 plus.minus sqrt(5), 2)$
  $ 
    a_n^(#text[общ.]) = c_1 (frac(1 + sqrt(5), 2))^n + c_2 (frac(1 - sqrt(5), 2))^n \
    cases(
      0 = c_1 + c_2,
      1 = c_1 dot frac(1 + sqrt(5), 2) + c_2 frac(1 - sqrt(5), 2)
    ) \
    c_1 = (sqrt(5))^(- 1) quad c_2 = (-sqrt(5))^(-1) \
    F_n = frac((frac(1 + sqrt(5), 2))^n - (frac(1 - sqrt(5), 2))^n, sqrt(5)) #text[ --- Формула Бине]
  $
]
#remark()[
  $ frac(1 + sqrt(5), 2) = Phi quad frac(1 - sqrt(5), 2) = Psi$
]
== Рекуррентные соотношения. Однородные рекуррентные соотношения с кратными корнями.

#remark()[
  $lambda_1$ --- корень характеристического уравнения кратности $2$
  $ 
    a_n^(#text[общ.]) = c_1 lambda_1^n + c_2 n lambda_1^n \
    (n + 2) lambda_1^(n + 1) = b(n + 1) lambda_1^n + c dot n lambda_1^(n - 1) \
    underbrace((n + 2) lambda^(n + 2), (a_(n + 2))) = b underbrace((n + 1) lambda_1^(n  +1 ), a_(n + 1)) + c underbrace(n lambda_1^n, a_n)
  $
] <second-case-roots>
== Рекуррентные соотношения. Однородные рекуррентные соотношения с комплексно-сопряженными корнями.
#lemma()[
  Формула Муавра
  $ (cos phi plus.minus i sin phi)^n = cos n phi plus.minus i sin n phi $
]

#remark()[
  Характеристическое уравнение имеет $2$ комплексных корня
  $ lambda_(1, 2) = alpha plus.minus beta i = r (cos phi plus.minus i sin phi) $
  - Если попали в #link(<first-case-roots>)[первый случай]
    $ 
      a_n^(#text[общ.]) = c_1 (alpha + beta i)^n + c_2 (alpha - beta i)^n = \
      = r^n ( c_1 (cos phi + i sin phi)^n  + c_2 (cos phi - i sin phi)^n) = \
      = r^n ((c_1 + c_2) cos (n phi) + i (c_1 - c_2) sin (n phi) ) = \
      = r^n (tilde(c_1) cos n phi + tilde(c_2) sin n phi)
    $
  - Если попали во #link(<second-case-roots>)[второй случай]
    $ a_(n + m) = b_1 dot a_(n + m - 1) + dots + b_m a_n + P(n) dot p^n $
    Алгоритм:
    1. Решаем ответствующее однородное уравнение
    2. Находим частное решение(я). Оно ищется в виде
      $ a_n^(#text[част.]) = Q(n) dot n^l dot p^n $
      , где $Q(n)$ --- произвольный многочлен такой же степени что и $P(n)$, $l$ --- кратность $p$ как корня характеристического уравнения из шага 1
    3. $a_n^(#text[общ.]) = a_n^(#text[одн.]) + a_n^(#text[част.]) + dots$
    4. подбор коэффициентов под начальные условия
]
== #todo() Рекуррентные соотношения. Неоднородные рекуррентные соотношения.
#remark()[
  $u(n) = P(n) dot sin (n phi) dot p^n$
  $ a_n^(#text[част.]) = Q(n) dot n^l (sin n phi + cos n phi) dot p^n $
]
== Теория вероятностей. Дискретная вероятность. Свойства. Условная вероятность. Примеры.
#definition()[
  $Omega = {omega_1, omega_2, dots, omega_n}$ --- *множество (пространство) элементарных исходов*.
  - Дизъюнктно --- если произошло одно не может произойти другое. $forall i,j, i != j:$ $omega_i$ и $omega_j$ --- *несовместны*
  - Нужно чтобы хотя бы 1 $omega_i$ произошло
  - Все $omega_i$ равновероятны
]

#definition()[
  $A$ --- *событие*, если $A subset Omega$
  $ PP(A) = (|A|) / (|Q|) $
]

#remark([Свойства])[
  1. $PP(emptyset) = 0$, $PP(Omega) = 1$, $forall A subset Omega, 0 <= PP(A) <= 1$
  2. $PP(A union B) = PP(A) + PP(B) - PP(A inter B)$
  Достаточно этих двух свойств
  3. $A inter B = emptyset ==> PP(A union B) = PP(A) + PP(B)$
  4. $PP(A) = 1 - PP(overline(A))$
  5. $PP(A union B) <= PP(A) + PP(B)$
  6. ~
    $ PP(union.big_(i = 1)^m A_i) = sum_(i = 1)^m PP(A_i) - sum_(1 <= i < j <= m) PP(A_i inter A_j) + sum_(1 <= i < j < k <= m) PP(A_i inter A_j inter A_k) - dots + (-1)^(m - 1) PP(A_1 inter A_2 inter dots inter A_m) $
]

// FIXME: Use #ref
#proof([Свойство 6])[
  По индукции:

  База: $m = 2$ --- это Свойство 2
  
  Переход: $m - 1 mapsto m$
  $
    PP(union.big_(i = 1)^n A_i) = PP(union.big_(i = 1)^(m - 1) A_i union A_m) = PP(union.big_(i = 1)^(m - 1) A_i) + PP(A_m) - PP(union.big_(i = 1)^(m - 1) (A_i inter A_m)) = \

    xunderline(stroke: #red, sum_(i = 1)^(m - 1) PP(A_i)) -
    xunderline(stroke: #blue, sum_(1 <= i < j <= m - 1) PP(A_i inter A_j)) + dots + 
    xunderline(stroke: #red, PP(A_m)) - 
      xunderline(stroke: #blue, sum_(i = 1)^(m - 1) PP(A_i inter A_m)) - 
      sum_(1 <= i < j <= m - 1) PP(A_i inter A_j inter A_m) + dots = \
    = sum_(i = 1)^m PP(A_i) - sum_(1 <= i < j <= m) PP(A_i inter A_j) + dots
  $
]

#definition()[
  $ P(A | B) = frac(|A inter B|, |B|) = frac(PP(A inter B), PP(B)) quad PP(B) != 0 $
]
#remark([Свойства])[
  1. $PP(emptyset | B) = 0$, $PP(B | B) = 1$, более того если $B subset A$, то $PP(A | B) = 1$
  2. $A_1 inter A_2 = emptyset ==> PP(A_1 union A_2 | B) = PP(A_1 | B) + PP(A_2 | B)$
  3. $PP(A | B) = 1 - PP(overline(A) | B)$
]
#example()[
  $B$ --- выпало четное, $A$ --- выпало кратное $3$.
  $ P(A | B) = frac(1/ 6, 1/2) = 1/ 3 $
]

== Теория вероятностей. Формула полной вероятности. Формула и теорема Байеса. Примеры.
#theorem([Формула полной вероятности])[
  $Omega = union.sq.big_(i = 1)^m B_i$, тогда
  $ PP(A) = sum_(i = 1)^m PP(A | B_i) dot PP(B_i) $
]
#proof()[
  $ 
    sum_(i = 1)^m PP(A | B_i) dot PP(B_i) = sum_(i = 1)^m frac(PP(A inter B_i), PP(B_i)) dot PP(B_i) = PP(union.big_(i = 1)^m (A inter B_i)) = \
    = PP(A inter (union.big_(i = 1)^m B_i)) = PP(A inter Omega) = PP(A)
  $
]
#example()[
  $1$-ая корзина: 3 белых и 5 черных, $2$-ая корзина: 3 белых и 3 черных. 
  1. Перекладываем 2 шара из 1ой во 2-ую
  2. Выбираем шар из 2-ой корзины

  $A$ --- это белый шар. $PP(A) = ?$. $B_i$ --- переложили $i$ белых шаров
  $ PP(A | B_0) = 3 / 8 quad PP(A | B_1) = 4 / 8 quad PP(A | B_2) = 5 / 8 $
  $ PP(B_0) = frac(binom(5, 2), binom(8, 2)) = 5/8 dot 4/7 = 5/14 quad PP(B_1)  = 3 / 8 dot 2 / 7 = 3/28 quad PP(B_1) = 15 / 28 $
  $ PP(A) = PP(A | B_0) dot PP(B_0) + PP(A | B_1) dot PP(B_1) + PP(A | B_2) dot PP(B_2) = dots = 15/32 $
]
#theorem([Формула Байеса])[
  $PP(A) != 0, PP(B) != 0$, тогда
  $ PP(B | A) = frac(PP(A | B) dot PP(B), PP(A)) $
]
#proof()[
  $ frac(PP(A | B) dot PP(B), PP(A)) = frac(PP(A inter B) / PP(B) dot PP(B), PP(A)) = PP(A inter B) / PP(A) = PP(B | A) $
]
#theorem([Байеса])[
  $Omega = union.sq.big_(i = 1)^m B_i$, $PP(A) != 0$
  $ PP(B_k | A) = frac(PP(A | B_k) dot PP(B_k), sum_(i = 1)^m PP(A | B_i) dot PP(B_i)) $
]
#example()[
  Два кубика:
  1. обычный
  2. с гранями 1, 1, 2, 2, 3, 3
  Какая вероятность что мы бросили обычный кубик если выпала 2.

  $A$ --- выпала 2, $B_i$ --- кидали $i$-ый кубик
  $ PP(B_1 | A) = frac(PP(A | B_1) dot PP(B_1), PP(A | B_1) dot PP(B_1) + PP(A | B_2) dot PP(B_2)) $
  $ PP(B_1) = PP(B_2) = 1 / 2 quad PP(A | B_1) = 1 / 6 quad PP(A | B_2) = 1 / 3 $
  $ PP(B_1 | A) = 1 / 3 $
]

== Теория вероятностей. Независимость событий. Независимость в совокупности. Примеры.
// $ PP(A inter B) / PP(B) = PP(A | B) = PP(A) $
#definition()[
  Если $PP(A inter B) = PP(A) dot PP(B)$, то события $A$ и $B$ *независимы*
]
#definition()[
  $A_1, A_2, dots, A_m$ --- события. Называются *независимыми в совокупности*, если для любого поднабора индексов $j$:
  $ PP(A_(j_1) union A_(j_2) union dots union A_(j_k)) = PP(A_(j_1)) dot PP(A_(j_2)) dot dots dot PP(A_(j_k)) $
]
#remark()[
  Здесь $2^m - m - 1$ содержательных условий
]

#example([Пирамида кого-то])[
  Дан тетраедр с покрашеными сторонами:
  1. красный
  2. белый
  3. синий
  4. и красный и белый и синий
  $A$ --- на выпавшей грани есть белый цвет, $B$ --- синий, $C$ --- красный.
  $
    PP(A) = PP(B) = PP(C) = 1/ 2 \
    PP(A inter B) = PP(B inter C) = PP(C inter A) = 1 /4  \
    PP(A inter B inter C) = 1 / 4
  $
  Пример задачи где $P(A inter B) = P(A inter B inter C)$
]
== Теория вероятностей. Обобщение дискретной модели. Схема Бернулли. Вероятность количества успехов. Примеры.
#remark()[
  - $Omega = {omega_1, dots, omega_n}$
  - $p_1, dots, p_n : p_i >= 0 quad p_1 + p_2 + dots + p_n = 1$
  $ PP(A) = sum_(omega_i in A) p_i $

  Проверим свойства:
  1. $PP(emptyset) = 0$, $PP(Omega) = 1$, $A subset Omega: PP(A) in [0; 1]$
  2. $PP(A union B) = PP(A) + PP(B) - PP(A inter B)$
    - $omega_i in A and omega_i in.not B$. В левую часть внесет $p_i$ и в правую $p_i$.
    - $omega_i in.not A and omega_i in B$. Аналогично
    - $omega_i in A and omega_i in B$. Внесет вклад в левую часть $p_i$. В правую часть $2 p_i - p_i = p_i$
]

#remark()[
  - $Omega = { omega : (x_1, x_2, dots, x_n) }, x_i in {0, 1}$
  - $p in [0; 1]: PP({omega}) = p^(sum x_i) dot (1 - p)^(sum x_i)$

  "0" --- решка, неудача. "1" --- орел, удача. Тогда $S_n = sum x_i$ --- количество успехов в схеме Бурнулли.
]

#remark()[
  $PP(S_n = k) = binom(n, k) p^k (1 - p)^(n - k)$
]

#remark()[
  $ sum^n_(k = 0) PP(S_n = k) = sum^n_(k = 0) binom(n, k) p^k (1 - p)^(n - k) = (1 + (1 - p))^n = 1 $
]
== Теория вероятностей. Теорема Пуассона. Примеры.
#theorem("Пуассона")[
  $n p_n = lambda$, тогда
  $ PP(S_n = k) -->_(n -> + infinity) (lambda ^k dot e^(- lambda)) / k! $
]
#proof()[
  $ PP(S_n = k) = binom(n, k) p_n^k (1 - p_n)^(n - k) = (n (n - 1)(n-  2) dots (n - k + 1)) / k! dot lambda^k / n^k dot (1 - lambda /n)^n dot (1 - lambda /n)^(-k) = \
    = lambda^k / k! dot n / n dot underbrace((n - 1) / n, -> 1) dot underbrace((n - 2) / n, -> 1) dots (n - k + 1) / n dot underbrace((1 - lambda / n)^n, -> e^(- lambda)) dot underbrace((1 - lambda /n)^(-k), -> 1) --> (lambda^k dot e^(- lambda)) / k!
  $
]


#remark()[
  Теорема верна и при $n p_n --> lambda$.
]
#remark()[
  В практическом приенении имеет смылсл только при больших $n$ и $k <= sqrt(n)$
]

#example()[
  Рулетка. Элементарные исходы $0, dots, 36$. Всегда ставим на $7$. $p = 1 / 37, 1-p = 36 / 37$.
  $ PP(S_111 = 2) = binom(111, 2) approx 0.225044 \
    PP(S_111 = 2) approx (3^2 e^(-3)) / 2! = 9 / 2 dot e^(-3) approx 0.22404
  $
  $lambda = 111 dot 1/37 = 3$
]
== Теория вероятностей. Локальная теорема Муавра-Лапласа (б/д). Примеры.
#theorem("Муавра-Лапласа")[
  $p in (0; 1)$ --- $"const"$, $q = 1 - p$, $x_k = (k - n p) / sqrt(n p q)$. Если при $n -> infinity$ $x_k$ меняется так, что $exists T med |x_k| <= T$. Тогда
  $ PP(S_n = k) ~ 1 / sqrt(2 pi n p q) dot e^(-x_k^2 / 2)  $
]

#remark()[
  Получаем хорошее приближение при $k$ близких к $n p$.
]
#example()[
  Ставим на красное $p = 18 / 37, q = 19 / 37$.
  $ PP(S_222 = 111) = binom(222, 111) (18 / 37)^111 dot (19 / 37)^111 approx 0.04932 \
    x = (111 - 108) / sqrt((108 dot 19) / 37) quad PP(S_222 = 111) = 1 / sqrt(2 pi (108 dot 19) / 37) e^(- 3^2 / (2 dot (108 dot 19) / 37)) approx 0.04935
  $
]

== Теория вероятностей. Интегральная теорема Муавра-Лапласа (б/д). Примеры.
#theorem("Интегральная теорема Муавра-Лапласа")[
  $ PP(a <= (S_n - n p) / sqrt(n p q) <= b) -->_(n -> + infinity) 1 / sqrt(2 pi) integral_a^b e^(-x^2 / 2) d x $
]
#remark()[
  $ 1 / sqrt(2 pi) integral_(- infinity)^t e^(- x ^2 / 2) d x = Phi(t) $
  $Phi(-t) = 1 - Phi(t)$
]
#remark()[
  $ PP(a <= S_n <= b) = PP((a - n p) / sqrt(n p q) <= (S_n - n p) / sqrt(n p q) <= (b - n p) / sqrt(n p q)) approx Phi((b - n p) / sqrt(n p q)) - Phi((a - n p) / sqrt(n p q))
  $
]
#remark()[
  Если вычтем малое число из $b$, то потеряем целый 1 случай, но в контексте $Phi$ значение почти не поменяется. В качестве $a$ и $b$ подставляем $ZZ + 1 / 2$.
]

#example()[
  Задача о гардеробе. В театре с 1600 мест, есть два гардероба, в который равновероятно приходят люди. Сколько мест надо выделить в гардеробе чтобы он не часто переполнялся (что гардероб не переполнится с вероятностью $29 / 30$).

  Размер гардероба $c$.
  $ PP(1600 - c <= S_1600 <= c) = 29/30 $
  $ PP((800 - c) / 20 <= (S_1600 - 800) / 20 <= (c - 800) / 20) approx 1 / sqrt(2 pi) integral^((c - 800) / 2)_((800 - c) / 20) e^(-x^2 / 2) d x = 29 / 30 = $
  $ = Phi((c - 800) / 20) - Phi((800 - c)/ 20) = 2 Phi((c - 800) / 20) - 1 >= 29 / 30 $
  $c = 843$
]
== Теория вероятностей. Колмогоровская модель теории вероятностей. Проверка выполнения свойств, доказанных в дискретном случае.
#definition()[
  $(Omega, cal(F), PP)$ --- вероятностное пространство. 
  - $Omega$ --- множество элементарных исходов (больше не дискретное)
  - $cal(F)$ --- $sigma$-алгебра событий
  - $PP$ --- мера на $cal(F)$ и $PP(Omega) = 1$
]

#remark()[
  $cal(S)$ --- $sigma$-алгебра над пространством $X$, если:
  1. $X in cal(S)$
  2. $X_1, X_2, dots : X_i in cal(S) ==> union.big_(i = 1)^infinity X_i in cal(S)$
  3. Если $A in cal(S)$, то $X \\ A in cal(S)$

  Следует что пустое, пересечение тоже в $cal(S)$.
]

#remark()[
  $PP$ --- мера, если:
  1. $PP(emptyset) = 0$
  2. $PP(A) >= 0$
  3. $A_1, A_2, dots$ --- попарно несовместные ($forall i != j: A_i inter A_j = emptyset$) события
    $ PP(union.big_(i = 1)^infinity A_i) = sum_(i = 1)^infinity PP(A_i) $
]

#properties()[
  Проверим два свойства которые раньше требовали:
  3. Если $A inter B = emptyset$, то $PP(A union B) = PP(A) + PP(B)$
    #proof()[
      В свойство 3. меры подставляем $A_1 = A, A_2 = B, A_i = emptyset$.
    ]
  2. Если $A subset B$, то $PP(A) <= PP(B)$.
    #proof()[
      $B = A union (B \\ A)$, а $A inter (B \\ A) = emptyset$
      $ PP(B) = PP(A) + underbrace(PP(B \\ A), >= 0) >= PP(A) $
    ]
  3. $forall A in cal(F) quad 0 <= PP(A) <= 1$
    #proof()[
      $emptyset subset A subset Omega$ + свойство 2.
    ]
  4. $PP(A union B) = PP(A) + PP(B) - PP(A inter B)$
    #proof()[
      $A union B = A union (B \\ A)$, а $A inter (B \\ A) = emptyset$. Можно применить свойство 1.:
      $ PP(A union B) = PP(A) + PP(B \\ A) $
      $B = (A inter B) union (B \\ A)$, а $(A inter B) inter (B \\ A) = emptyset$
      $ PP(B) = PP(A inter B) + PP(B \\ A) ==> PP(B \\ A) = PP(B) - PP(A inter B) \
        PP(A union B) = PP(A) + PP(B) - PP(A inter B)
      $
    ]
]

#definition()[
  $A_1, A_2, dots$ называются независимыми (в совокупности). Если для любого конечного набора индексов $PP(inter.big_(i = 1)^n A_(k_i)) = product_(i = 1)^n PP(A_(k_i))$
]
#remark()[
  $PP(inter.big_(i = 1)^infinity A_i) = product_(i = 1)^infinity PP(A_i)$
  $ PP(inter.big_(i = 10)^infinity A_i) =^1 lim_(n -> infinity) PP(inter.big_(i = 1)^n A_i) = lim_(n -> + infinity) product_(i = 1)^n PP(A_i) = product_(i = 1)^infinity PP(A_i) $
  1. 
    $ lim_(n -> + infinity) PP(overbrace(inter.big_(i = 1)^n A_i, B_n)) =#pin(1) PP(inter.big_(i = 1)^infinity B_i) = PP(inter.big_(i = 1)^infinity A_i) $
    #pinit-point-from(1)[по непрерывности меры] \
    По непрерывности меры: $lim_(n -> infinity) PP(B_n) = PP(inter.big_(i = 1)^infinity B_i)$
]
== Теория вероятностей. Случайные величины. Распределение. Функция распределения и ее свойства.
#definition()[
  *Случайной величиной* (с.в.) называется $xi : Omega -> RR$ измеримая
]
#remark()[
  Измеримая --- если попали в какой-то элемент $sigma$-алгебры в $RR$, то должны попасть в элемент $sigma$-алгебры в $Omega$
]

#definition()[
  *Распределение случайной величины* $P_xi$ --- мера, заданная на борелевской $sigma$-алгебре $frak(B)$.
  $ P_xi (A) colon.eq PP(xi in A) = PP(omega in Omega : xi(omega) in A) $
]

#remark()[
  Случайные величины $xi$ и $eta$ совпадают если $P_xi (A) = P_eta (A)$ для любого $A$ --- борелевского. Но на самом деле достаточно совпадения на ячейках $(a; b]$.
  $ P_xi ((a; b]) = PP(a < xi <= b) = PP(xi <= b) - PP(xi <= a) $
  То есть необходимо и достаточно $forall c quad PP(xi <= c) = PP(eta <= c)$
]

#definition()[
  $F_xi (t) colon.eq PP(xi <= t)$ называется функцией распределения случайной величины $xi$.
]

#properties()[
  1. Случайная величина однозначно задается своей функцией распределения
  2. $forall t quad 0 <= F_xi (t) <= 1$ --- очевидно
  3. $F_xi (t)$ нестрого возрастает
    #proof()[
      $t < s$, проверим что $F_xi (t) <= F_xi (s)$.
      $ F_xi (t) = PP(xi <= t) <=^? PP(xi <=s ) = F_xi(s) $
      Потому что ${xi <= t} subset {xi <= s}$
    ]
  4. $F_xi (t) -->_(t -> +infinity) 1$ и $F_xi (t) -->_(t -> - infinity) 0$
    #proof()[
      $F_xi (t) -->_(t -> -infinity) 0$ ? $t_n$ монотонно убывает к $- infinity$.
      $ {xi <= t_n} = B_n ==> B_1 supset B_2 supset B_3 supset dots $
      $ lim_(n -> +infinity) PP(B_n) = lim_(n -> +infinity) F_xi (t_n) = lim_(t -> - infinity) F_xi (t) $
      По непрерывности меры (сверху?) $lim_(n -> +infinity) PP(B_n) = PP(inter_(i = 1)^infinity B_i) = PP(emptyset) = 0$
    ]
  5. $F_xi (t)$ непрерывна справа. $lim_(t_n -> t+) F_xi (t_n) = F_xi (t)$
    #proof()[
      $t_n$ монотонно убывают к $t$
      $ { xi <= t_n } = B_n quad B_1 supset B_2 supset dots $
      $ lim_(t_n arrow.br t) PP_(B_n) = lim_(t_n -> t+) F_xi (t_n) $
      По непрерывности меры $lim_(t_n arrow.br t) PP_(B_n) = PP(inter.big_(i = 1)^infinity B_i) = PP(xi <= t) = F_xi (t)$
    ]
  6. $PP(xi < t) = lim_(x -> t-) F_xi (x)$
    #proof()[
      $t_n$ монотонно возрастают к $t$
      $ {xi <= t_n) = B_n quad B_1 subset B_2 subset dots $
      $ lim_(t_n arrow.tr t) PP(B_n) = lim_(x -> t) F_xi (x) $
      $ lim_(t_n arrow.tr t) PP(B_n) = PP(union.big_(i = 1)^infinity B_i) = PP(xi < t) $
    ]
  7. $F_(xi + c) (t) = F_xi (t - c)$
    #proof()[
      $ F_(xi + c) (t) = PP(xi + c <= t) = PP(xi <= t - c) = F_xi (t - c) $
    ]
  8. $c > 0 quad F_(c xi) (t) = F_xi (t / c)$
]

#remark()[
  Любая функция удовлетворяющая свойствам 3-5 это функция распределения какой-то случайно величины
]
== Теория вероятностей. Дискретные распределения. Абсолютно непрерывные распределения. Плотность распределения и ее свойства.
#definition()[
  Дискретной случайной величиной называется $xi$ у которой не более чем счетная область значений. $xi(omega) in {y_1, y_2, dots}$. Распределение однозначно задается $PP(xi = y_i)$
  $ P_xi (A) = sum_(y_i in A) PP(xi = y_i) $
]
#remark()[
  А функция дискретной случайной величины выглядит так:
  $y_1 < y_2 < dots $ --- ступенчатая функция
]

#definition()[
  *Непрерывная случайная величина* -- вероятность принять любое конкретное значение равно $0$, т.е. $forall c quad PP(xi = c) = 0$.
]
#remark()[
  Тогда у нее непрерывная функция распределения
  $ lim_(x -> t-) F_xi (x) = PP(xi < t) = PP(xi < t) + PP(xi = t) = PP(xi <= t) = F_xi (t) $
]

#definition()[
  Если существует $p_xi (t) : RR -> RR$ измеримая:
  $ F_xi (t) = integral_(-infinity)^t p_xi (t) d t $
  , то $xi$ называется *абсолютно непрерывной случайной величиной*, а $p_xi (t)$ называется *плотностью распределения*
    
]

#properties()[
  1. $PP(xi in A) = integral_A p_xi (t) d t$
  2. $integral_RR p_xi (t) d t = 1$
  3. $p_xi (t) = F'_xi (t)$ почти во всех $t$
]
== #todo() Теория вероятностей. Совместное распределение. Независимые с.в. Равносильные условия независимости.
#definition()[
  Случайные величины $xi_1, xi_2, dots, xi_n$ называются независимыми, если $forall A_1, A_2, dots, A_n$ --- борелевских подмножеств $RR$: события ${xi_1 in A_1}, {xi_2 in A_2}, dots, {xi_n in A_n}$.

  *или* $PP(xi_1 in A_1, xi_2 in A_2, dots, x_n in A_n) = PP(xi_1 in A_1) dot PP(xi_2 in A_2) dot dots dot PP(xi_n in A_n)$
]

#definition()[
  Случайные величины $xi_1, xi_2, dots$ называются независимыми если $forall n quad xi_1, xi_2, dots, xi_n$ --- независимы.
]

#symb()[
  $arrow(xi) = (xi_1, dots, xi_n)$
]

#definition()[
  Совместным распределением $arrow(xi)$ называется мера $Rho_arrow(xi)$ заданная на всех борелевских подмножества $RR^n$: \
  $Rho_arrow(xi) ( B) colon.eq PP(arrow(xi) in B) = PP(omega in Omega : (xi_1(omega), xi_2(omega), dots, xi_n (omega)) in B)$.
]

#statement()[
  $xi_1, dots, xi_n$ независимы $<==>$  $Rho_arrow(xi) = Rho_(xi_1) times Rho_(xi_2) times dots times Rho_(xi_n)$
]
#proof()[
  - "$<==$"
    $ Rho_arrow(xi) (B) = PP(arrow(xi) in B) = PP((xi_1, dots, xi_n) in B_1 times B_2 times dots times B_n) = PP(xi_1 in B_1, xi_2 in B_2, dots, xi_n in B_n) = \
      = PP(xi_1 in B_1) dot PP(xi_2 in B_2) dot dots dot PP(xi_n in B_n) = Rho_(xi_1) (B_1) times dots times Rho_(xi_n) (B_n)
    $
  - "$==>$" проверим на ячейках 
    $ PP(arrow(xi) in (a; b]) = PP(xi_1 in (a_1; b_1], dots, xi_n in (a_n; b_n]) = PP(xi_1 in (a_1; b_1]) dot dots dot PP(xi_n in (a_n; b_n]) $
    #todo()
]
== Теория вероятностей. Совместная функция распределения и ее свойства. Совместная плотность.
#definition()[
  Совместной функцией распределения $F_arrow(xi) (arrow(x))$ называется функция $RR^n -> RR$:
  $ F_arrow(xi) (arrow(x)) = PP(xi_1 <= x_1, xi_2 <= x_2, dots, xi_n <= x_n) $
]

#definition()[
  Совместной плотностью $p_arrow(xi) (arrow(x))$ называется измеримая функция $RR^n -> RR_+$ :
  $ F_arrow(xi) (arrow(x)) = integral_(- infinity)^(x_1) dots integral_(- infinity)^(x_n) p_arrow(xi) (t_1, t_2, dots, t_n) d t_n dots d t_1 $
]

#statement()[
  1. $xi_1, dots, xi_n$ --- независимые $<==>$ $F_arrow(xi) (arrow(x)) = F_(xi_1) (x_1) dot F_(xi_2) (x_2) dot dots dot F_(xi_n) (x_n) $
  2. $xi_1, dots, xi_n$ --- абсолютно непрерывны
  $xi_1, dots, xi_n$ --- независимы $<==>$ совместная плотность существует и $p_arrow(xi) (arrow(x)) = p_(xi_1) (x_1) dot dots dot p_(xi_n) (x_n)$
]

#remark()[
  По совместному распределению можно найти распределение любой компоненты.
  $ P_(xi_k) (B_k) = PP(xi_k in B_k) = PP(xi_1 in RR, dots, xi_(k - 1) in RR, xi_k in B_k, dots, xi_n in RR) = PP_arrow(xi) (RR^(k - 1) times B times RR^(n - k)) $

  В обратную сторону неверно $xi, eta in {0, 1}$ с вероятностью $1/2$. $angle.spheric (xi, eta)$:
  1. $xi = eta quad (xi, eta) in {(0, 0), (1, 1)}$ с вероятностью $1/2$
  2. $xi != eta quad (xi, eta) in {(1, 0), (0, 1)}$ с вероятностью $1/2$
]
== #todo() Теория вероятностей. Математическое ожидание. Свойства. Неравенство Маркова. Примеры. 
#definition()[
  Математическое ожидание $EE_xi$
  $ EE xi = integral_Omega xi (omega) d PP(omega) $
]

#properties()[
  1. $EE xi$ --- линейно : $EE(a xi + b eta) = a EE xi + b EE eta$
  2. $xi >= 0$ с вероятностью $1$ $==>$ $EE xi >= 0$ (вместо $0$ можно любую константу)
  3. $xi >= eta$ с вероятностью $1$ $==>$ $EE xi >= EE eta$ (следует из двух предыдущих)
  4. $EE xi = integral_RR x d P_xi (x)$
  5. $EE f(xi_1, xi_2, dots, xi_n) = integral_(RR^n) f(t_1, dots, t_n) d P_arrow(xi) (t_1, dots, t_n)$, где $f$ --- измерима
  6. Если $xi$ и $eta$ --- независимы, то $EE xi eta = EE xi dot EE eta$
    #proof()[
      $ EE xi eta = integral_(R^2) x y d P_((xi, eta)) (x, y) = integral_(R^2) x y d P_xi (x) d P_eta (y) = integral_R x d P_xi (x) dot integral_R y d P_eta (y) = EE xi dot EE eta $
    ]
  7. Неравенство Гёльдера $p, q > 1 : 1/p  + 1/q = 1$
    $ EE |xi eta| <= (EE |xi|^p)^(1/p) dot (EE |eta|^q)^(1/q) $
  8. Неравенство Ляпунова $0 < r < s$
    $ (EE |xi|^r)^(1/r) <= (EE |xi|^s)^(1/s) $
    #proof()[
      $p = s/r > 1, q = p / (p - 1) quad 1 / p + (p - 1) / p = 1$
      $ EE |xi^r dot 1| <= (EE |xi^r|^(s / r))^(r / s) dot (EE |1|^q)^(1 / q) ==> EE |xi|^r <= (EE |xi|^s)^(r / s) $
    ]
  9. Неравенство Маркова $xi >= 0, t, p > 0$
    $ PP(xi >= t) <= (EE xi^p) / (t^p) $
    #proof()[
      $ EE xi^p = integral_RR x^p d P_xi (x) = integral_0^t x^p d P_xi (x) + integral_t^(+infinity) x^p d P_xi (x) >= integral_t^(+infinity) t^p d P_xi (x) = \
        = t^p dot integral_t^(+infinity) 1 dot d P_xi (x) = t^p dot PP(xi >= t)
      $
    ]
]
== #todo() Теория вероятностей. Дисперсия. Свойства. Неравенство Чебышева. Примеры.
#definition()[
  *Дисперсией* случайной величины называется $DD xi = "Var" xi colon.eq EE (xi - E xi)^2$
]

#properties()[
  1. $DD xi = EE xi^2 - EE^2 xi$
    #proof()[
      $ EE (xi - EE xi)^2 = EE (xi^2 - 2 xi EE xi + EE^2 xi) = EE xi^2 - 2 EE xi dot EE xi + EE^2 xi = EE xi^2 - EE^2 xi $
    ]
  2. $DD (xi + a) = DD xi$
    #proof()[
        $ EE (xi + a - EE (xi + a))^2 = EE (xi - EE xi)^2 = DD xi $
    ]
  3. $DD (c xi) = c^2 DD xi$
    #proof()[
      $ EE (c xi - EE c xi)^2 = EE (c (xi - E xi))^2 = c^2 EE (xi - E xi)^2 = c^2 DD xi $
    ]
  4. $xi, eta$ --- независимы, то $DD (xi + eta) = DD xi + DD eta$
    #proof()[
      $ DD (xi + eta) = EE (xi + eta - EE xi - EE eta)^2 = EE ((xi - EE xi) + (eta - EE eta))^2 = \
      = EE ((xi - EE xi)^2 + (eta - EE eta)^2 - 2 (xi - EE xi) (eta - EE eta)) = DD xi + DD eta $
    ]
  5. $DD xi >= 0$ и $DD xi = 0 <==> $ $xi$ --- константа с вероятностью $1$
  6. $EE |xi - EE xi| <= sqrt(DD xi)$
    #proof()[Ляпунов.
      $EE |xi - EE xi| <= (EE |xi - EE xi|^2)^(1/2) = (DD xi)^(1/2)$
    ]
    $sqrt(DD xi) = sigma$ --- *стандартное отклонение*
  7. Неравенство Чернова $PP (|xi - EE xi| >= t) <= (DD xi) / t^2$
    #proof()[Неравенство Маркова для $p = 2$]
]

#theorem("Неравенство Чебышева")[
  $ PP(lr(|S_n / n - EE S_n / n|) >= epsilon) <= (DD S_n / n) / epsilon^2 --> 0 $
  #fixme()
]
== #todo() Теория вероятностей. Медиана. Моменты случайных величин. Примеры.

#definition()[
  *Медианой* случайной величины $xi$ называется $M in RR$: $PP(xi <= M) >= 1/2$ и $PP(xi >= M) >= 1/2$.
]
#definition()[
  - $EE xi^k$ --- $k$-тый момент
  - $EE |xi|^k$ --- $k$-тый абсолютный момент
  - $EE (xi - EE xi)^k$ --- $k$-тый центральный момент
  - $EE |xi - EE xi|^k$ --- $k$-тый центральный абсолютный момент
]

== #todo() Теория вероятностей. Ковариация. Коэффициент корреляции. Свойства. Примеры.
#definition()[
  Ковариация $xi$ и $eta$ : $EE ((xi - EE xi) (eta - EE eta)) eq.colon "cov"(xi, eta)$
]

#properties()[
  1. $"cov"(xi, xi) = DD xi$
  2. $"cov"(xi, eta) = "cov"(eta, xi)$
  3. $"cov"(xi, eta)$ --- линейна по каждой переменной
  4. $"cov"(xi, eta) = EE xi eta - EE xi dot EE eta$
    #proof()[
      $ EE((xi - EE xi) (eta - EE eta)) = EE (xi eta - eta dot EE xi - xi dot EE eta + EE xi dot EE eta) = \
        = EE xi eta - EE xi dot EE eta - EE eta dot EE xi + EE xi dot EE eta = EE xi eta - EE xi dot EE eta
      $
    ]
  5. Если $xi$ и $eta$ независимы то $"cov"(xi, eta) = 0$
    #remark()[
      Почему в обратную сторону не верно. $xi = cases(-1 "," 1/3, 0 "," 1/3, 1 "," 1/3)$. $eta = xi^2$.
      Очевидно что они зависимы. Покажем что ковариация не $0$:
      $ EE xi = 0 quad EE xi eta = EE xi^3 = EE xi = 0 quad EE xi eta = 0 = EE xi dot EE eta ==> "cov"(xi, eta) = 0 $
    ]
  6. $DD (xi + eta) = DD xi + DD eta + 2 "cov"(xi, eta)$
  7. $DD (sum_(i = 1)^n xi_i) = sum_(i = 1)^n DD xi_1 + 2 sum_(i < j) "cov"(xi_i, xi_j)$
    #proof()[
      $ DD (sum_(i = 1)^n xi_i) = EE (sum_(i = 1)^n xi_i - EE sum_(i = 1)^n xi)^2 = EE((sum_(i = 1)^n xi_i^2) + (EE sum_(i = 1)^n xi)^2 - 2 dot sum xi_i dot EE sum xi_i) = \
        = EE sum xi_i^2 + 2 EE sum_(i < j) xi_i xi_j + (EE sum xi_i)^2 - 2 (EE sum xi_i)^2 = EE sum xi_i^2 + 2 EE sum_(i < j) xi_i xi_j - (sum EE xi_i)^2 = \
        = xunderline(stroke: #blue, EE sum xi_i^2) + xunderline(stroke: #green, 2 EE sum_(i < j) xi_i xi_j) - xunderline(stroke: #blue, sum EE^2 xi_i) - xunderline(stroke: #green, 2 sum_(i < j) EE xi_i EE xi_j) = xunderline(stroke: #blue, sum_(i = 1)^n DD xi_i) + xunderline(stroke: #green, 2 sum_(i < j) "cov"(xi_i, xi_j))
      $
    ]
]

#definition()[
  $r(xi, eta)$ --- коэффициент корреляции $xi$ и $eta$
  $ r(xi, eta) colon.eq ("cov"(xi, eta))/sqrt(DD xi dot DD eta) $
]
#properties()[
  1. $r(xi, eta) in [-1, 1]$ (по свойству 8 (неравенство КБШ)
  2. $r(xi, eta) = r(eta, xi)$
  3. $r(a xi + b, c eta + d) = "sign"(a dot c) dot r(xi, eta)$
    #proof()[
      $ r(a xi + b, c eta + d) = ("cov"(a xi + b, c eta + d)) / sqrt(DD (a xi + b) dot DD (c eta + d)) = (a c dot "cov"(xi, eta)) / sqrt(a^2 dot DD xi dot c^2 dot DD eta)  = (a c dot "cov"(xi, eta)) / (|a c| sqrt(DD xi dot DD eta))$
    ]
  4. $r(xi, xi) = 1$
  5. $xi$, $eta$ --- независимые $==> r(xi, eta) = 0$
  6. $r(xi, eta) = plus.minus 1 <==> xi = a eta + b$ (причем знак $r$ совпадает со знаком $a$)
    #proof()[
      - $(<==)$ доказано по предыдущим свойствам
      - $(==>)$ $angle.spheric xi' = xi / sqrt(DD xi), eta' = eta/sqrt(DD eta)$
        $ plus.minus 1 = r(xi, eta) = "cov"(xi, eta) / sqrt(DD xi dot DD eta) $
        $ angle.spheric DD (xi' - eta') = DD xi' + DD eta' - 2 "cov"(xi', eta') = 2 - 2 dot ("cov"(xi, eta)) / sqrt(DD xi dot DD eta) = 0 $
        $ D xi' = DD ((xi - EE xi) / sqrt(DD xi)) = 1 / (DD xi) dot DD (xi - EE xi) = 1 $
      #todo()
    ]
]

== #todo() Теория вероятностей. Определение видов сходимости с.в. и их связь. Контрпримеры для всех ситуаций, когда «стрелочки» нет.
$xi_1, xi_2, dots$ --- случайные величины : $Omega -> RR$

#definition()[
  $xi_n -> xi$ почти наверное
  $ PP(omega in Omega : xi_n (omega) -->_(n -> infinity) xi(omega)) = 1 $
]

#definition()[
  $xi_n -->_(n -> infinity)^(L_p) xi$ сходится в среднем порядка $p$
  $ EE |xi_n - xi|^p --> 0 $
]

#definition()[
  $xi_n -->^PP xi$ по вероятности
  $ forall epsilon > 0 quad PP(|xi_n - xi| > epsilon) -->_(n -> infinity) 0 $
]

#definition()[
  $xi_n -->^d xi$ сходимость по распределению
  $ forall x in C_(F_xi) quad F_(xi_n)(x) --> F_xi (x) $
  $C_(F_xi)$ --- точки непрерывности $F_xi$.
]

#remark()[
- 1. $arrow.double.not$ 2. (тогда и 3. $arrow.double.not$ 2.)
  #proof()[
    $Omega : [0; 1] quad xi_n = n^p dot bb(1)_([0; 1/n]) quad xi_n --> 0$ почти наверное
    $ EE |xi_n - 0|^p = EE n dot bb(1)_([0; 1/n]) = n dot EE bb(1)_([0; 1/n]) = n dot 1 / n = 1 arrow.not 0 $
  ]
- 2. $arrow.double.not$ 1. (тогда и 3. $arrow.double.not$ 1.)
  #proof()[
    Рассмотрим последовательность $eta_(1, 0), eta_(2, 0), eta_(2, 1), eta_(3,0), eta_(3,1), eta_(3, 2), dots$
    $ eta_(n,k) = bb(1)_([k / n; (k + 1) / n]) quad EE |eta_(n, k) - 0|^p = 1/n --> 0 $
    $eta_(n, k) arrow.not 0$ почти наверное
  ]
- 4. $arrow.double.not$ 3. (тогда и 4. $arrow.double.not$ 1. и 4. $arrow.double.not$ 2.)
  #proof()[
    $xi_1, xi_2, dots$ --- н.о.р.с.в (независимые и одинаково распределенные случайные величины). $F_(xi_n) (x) --> F_xi (x)$ (это буквально один ф.р)
    $ epsilon = 1/2 quad PP(|xi_n - xi| > 1/2) = 1/2 arrow.not 0 $
  ]
]

== Теория вероятностей. Вывод сходимости по вероятности из других видов сходимости.
#remark()[
- 1. $==>$ 3. по т. Лебега
- 2. $==>$ 3.
  #proof()[
    $forall epsilon  quad PP(|xi_n - xi| > epsilon) <= (EE |xi_n - xi|^p) / epsilon^p --> 0$ по неравенству Маркова
  ]
]

#task(numbering: (..) => numbering("1", 3))[
  Пусть $xi_n -->^d c$. Докажите что тогда $xi_n -->^PP c$
]
#solution()[
  $F_(xi_n) (x) --> F_c (x) quad forall x in C_(F_(xi_n))$. Заметим что $F_c(x) = PP(c <= x)$. При $x < c$ $F_(xi_n) (x) --> 0$, а при $x > c$ $F_(xi_n) (x) --> 1$. Хотим доказать что $forall epsilon > 0 : PP(|xi_n - c| <= epsilon) --> 1$
  $ PP(-epsilon + c <= xi_n <= xi + c) = underbrace(F_(xi_n) (c + epsilon), --> 1) - underbrace(F(xi_n) (c - epsilon), --> 0) + PP(xi_n = c - epsilon) $
  $ PP(xi_n <= c - epsilon/2) = PP(xi_n <= (3 epsilon) / 2) + PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]) $
  $ underbrace(PP(xi_n <= c - epsilon/2), --> 0) - underbrace(PP(xi_n <= (3 epsilon) / 2), --> 0) = PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]) $
  $ underbrace(PP(xi_n in (c - (3 epsilon) /2; c - epsilon / 2]), --> 0) <= PP(c - epsilon - xi_n) --> 0 $
]

== Теория вероятностей. Связь сходимости по вероятности и сходимости по распределению.
#remark()[
- 3. $==>$ 4.
  #proof()[
      $forall epsilon PP(|xi_n - xi| > epsilon) --> 0$. Хотим проверить что $F_(xi_n) (x) --> F_xi(x)$, т.е. $PP(xi_n <= x) --> PP(xi <= x)$.
      1. ${xi_n <= x} supset {xi + epsilon <= x} \\ {|xi_n - xi| > epsilon}$
        $ PP(xi_n <= x) >= PP({xi + epsilon <= x} \\ {|xi_n - xi| > epsilon}) >= PP(xi + epsilon <= x) - PP(|xi_n - xi| > epsilon) $
        $ underline(lim) PP (xi_n <= x) >= F_xi (x - epsilon) $
      2. ${xi_n > x} supset {xi - epsilon > x} \\ {|xi_n - xi| > epsilon}$
        $ PP(xi_n > x) >= PP(xi - epsilon > x) - PP(|xi_n - xi| > epsilon) $
        $ 1 - PP(xi_n <= x) >= 1 - F_xi(x + epsilon) - PP(|xi_n - xi| > epsilon) $
        $ PP(xi_n <= x) <= F_xi(x + epsilon) + PP(|xi_n - xi| > epsilon) $
        $ overline(lim) PP(xi_n <= x) <= F_xi (x + epsilon) $
      $ F_xi (x - epsilon) <= underline(lim) F_(xi_n) (x) <= overline(lim) F_(xi_n) (x) <= F_xi (x + epsilon) $
      $ underline(lim) = overline(lim) = lim = F_xi (x) $
  ]
]
== #todo() Теория вероятностей. Закон больших чисел. Примеры использования. Выводы из ЗБЧ.
#theorem([Закон больших чисел (ЗБЧ)])[
$xi_1, xi_2, dots$ --- попарно некоррелируемы. $exists M med forall i quad DD xi_i <= M$. Пусть $S_n = xi_1 + dots + xi_n$. Тогда
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
== #todo() Теория вероятностей. Усиленный ЗБЧ (б/д). Центральная предельная теорема (б.д.). Примеры использования. Выводы из ЦПТ.
#theorem([Усиленный закон больших чисел (УЗБЧ)])[
  $x_1, xi_2, dots$ --- независимые. $exists M med forall i quad EE xi_i^4 <= M$. Тогда
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
== Графы. Основные определения (простые графы, орграфы, псевдо и мультиграфы, инцидентность, смежность, степени вершин). Лемма о рукопожатиях. 
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
  Если $"deg"(v) = 0$, то $v$ --- изолированная вершина. Если $"deg"(v) = 1$ то $v$ --- висячая вершина.

]
#symb()[
  $max_(v in V(G)) "deg"(v) eq.colon Delta(G)$
]
#symb()[
  $min_(v in V(G)) "deg"(v) eq.colon delta(G)$
]
== Графы. Основные определения (маршруты, пути и простые пути в графах, замкнутые маршруты, циклы и простые циклы). Связность.
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

#definition()[
  Если между любыми двумя вершинами графа есть путь, то граф *связный*.
]

#remark()[
  Т.к. отношение связности это отношение эквивалентности, то любой граф можно разбить на связные подграфы --- факторизовать.
]

#definition()[
  Такие подграфы называются *компонентами связности*.
]

#symb()[$c(G)$ --- количество компонент связности графа $G$]

#definition()[
  Граф называется *регулярным*, если все степени вершин равны. Если они равны $k$, то говорим что граф $k$-регулярный.
]
#remark()[
  Кубический граф --- $3$-регулярный
]
#remark()[
  Для $k$-регулярного графа
  $ |E(G)| = (|V(G)| dot k) / 2 $
]

#definition()[
  Граф без кратных ребер и петель называется *простым*.
]

#remark()[
  С этого момента считаем все графы простыми
]

#definition()[
  Граф называется *полным* если две любые его вершины смежны
]
#symb()[$K_n$]
#remark()[$|E(G)| = (n (n - 1)) / 2$, где $n = |V(G)|$]

#definition()[
  $overline(G)$ --- называется дополнением графа $G = angle.l V(G), E(G) angle.r$, если $V(overline(G)) = V(G)$ и $E(overline(G))$ такое что:
  - $E(overline(G)) inter E(G) = emptyset$
  - $E(overline(G)) union E(G) = E(K_n)$, где $n = |V(G)|$
]
== Графы. Деревья. Основные определения. Вспомогательные утверждения.
#definition()[
  *Дерево* --- связный граф без циклов
]

#definition()[
  *Лес* --- граф без циклов
]

#definition()[
  *Мост* --- ребро при удалении которого увеличивается количество компонент связности
]

#statement()[
  $e$ --- мост $<==>$ не существует цикла содержащего $e$.
] <stmt-bridge-no-cycle>
#proof()[
  - $(==>)$ Пусть существует цикл содержащий $e$. Удалим $e$, количество компонент связности не увеличится, хотя $e$ --- мост. Противоречие
  - $(<==)$ Допустим что $e$ --- не мост. Удалим $e$. Пусть $e$ соединяло вершины $u$ и $v$. Т.к. $e$ не мост то в $G - {e}$ между $u$ и $v$ есть путь $u e_1 v_1 e_2 dots e_k v$. Вернем $e$, получим цикл с $e$. Противоречие.
]

#definition()[
  $T$ --- дерево. Если $"deg"(v) = 1$, то $v$ называется *листом*.
]

#statement()[
  В любом дереве ($|V(G)| >= 2$) есть хотя бы $2$ листа.
] <stmt-leaf>
#proof()[
  Рассмотрим путь наибольшей длины $v_1 e_1 v_2 e_2 dots v_(k - 1) e_(k - 1) v_k$. Докажем что $v_1$, $v_k$ --- листья. Пусть $v_k$ не лист, тогда существует $e_k$ инцидентное $v_k != e_k$.
  1. $e_k$ не может быть инцидентным $v_i$, $i in [1; k - 1]$ иначе будет цикл
  2. $e_k$ не может быть инцидентным вершинам не из пути, т.к. нашелся бы путь лучше
]

#statement()[
  $T$ --- дерево. $|E(T)| = |V(T)| - 1$.
] <stmt-tree-edges-vertices-number>
#proof()[
  Индукция по $n = |V(T)|$. \
  База: $n = 1$ --- очевидно \
  ИП: $k |-> k + 1$. Рассмотрим $T$ на $k + 1$ вершинах. У $T$ есть лист (по #ref(<stmt-leaf>, supplement: [утверждению])). Назовем его $v$. Рассмотрим $T - {v}$ --- это дерево на $k$ вершинах. По ИП 
  $ |E(T)| - 1 = |E(T - {v})| = |V(T - {v}| - 1 = |V(T)| - 2 ==> |E(T)| = |V(T)| - 1 $
]

#corollary_statement()[
  $G$ --- лес. $|E(G)| = |V(G)| - c(G)$
]
== Графы. Деревья. 5 определений и их эквивалентность.
#theorem()[
  $T$ --- дерево $<==>$ $T$ --- связный и $|E(T)| = |V(T)| - 1$.
]
#proof()[
  - $(==>)$ уже доказано
  - $(<==)$ Если в $T$ есть цикл, то удалим любое ребро этого цикла. Повторим пока не получим ацикличный граф. Этот граф $T'$ --- дерево. Значит $|E(T')| = |V(T')| - 1$.
  $ |E(T')| = |V(T')| - 1 = |V(T)| - 1 = |E(T)| $
  Значит не удалили никакие ребра, т.е. применили алогримт удаление ровно 0 раз. Значит изначально было дерево
]

#corollary()[
  $G$ --- связный, то $|E(G)| >= |V(G)| - 1$
]
#corollary()[
  В доказательстве представлен алгоритм получения остовного дерева
]

#theorem()[
  $T$ --- дерево $<==>$ $T$ --- ацикличен и $|E(T)| = |V(T)| - 1$
]
#proof()[
  - $(==>)$ уже знаем
  - $(<==)$ Если $T$ не связен, то добавим ребро между компонентами связности (циклы не появятся по #ref(<stmt-bridge-no-cycle>, supplement: [утверждению]))
    Повторяем пока получим связный граф. Тогда он будет деревом $T'$.
    $ |E(T')| = |V(T'| - 1 = |V(T)| - 1 = |E(T)| $
    Значит проделали добавление ребер ровно $0$ раз, значит $T'$ и есть $T$.
]

#theorem()[
  $T$ --- дерево $<==>$ $T$ --- связный и любое ребро $T$ --- мост.
]
#proof()[
  - $(==>)$  Связность есть. Пусть найдется ребро $e = u v$, не являющееся мостом. Значит в $T - {e}$ между $u$ и $v$ есть путь $u e_1 dots e_k v$. Тогда в $T$ есть цикл $u e_1 dots e_k v e u$. Значит $T$ --- не дерево. Противоречие.
  - $(<==)$ Связность есть. Ацикличность следует из #ref(<stmt-bridge-no-cycle>, supplement: [утверждения])
]

#theorem()[
  $T$ --- дерево $<==>$ между любыми двумя вершинами существует единственный путь
]
#proof()[
  - $(==>)$ существование следует из связности. Единственность из ацикличности
  - $(<==)$ из существования следует связности. Из единственности ацикличность
]
== #todo() Графы. Эйлеровы графы. Теорема Эйлера. Примеры использования.
#definition()[
  Путь или цикл называется *эйлеровым* если он проходит по всем ребрам.
]

#definition()[
  Если в графе есть эйлеровый цикл, то граф называется *эйлеровым*. Если нет цикла, но есть путь, то *полуэйлеровым*
]

#theorem([Эйлера])[
  $G$ --- связный (содержит ровно одну нетривиальную компоненту связности)
  1. $G$ --- эйлеров $<==>$ $forall v in V(G): "deg"(v) divides 2$
  2. $G$ --- полуэйлеров $<==>$ $exists v_1, v_2 : "deg"(v_1) divides.not 2, "deg"(v_2) divides.not 2, forall v in V(G) \\ {v_1, v_2} med "deg"(v) divides 2$. Более того $v_1$ и $v_2$ будут началом и концом эйлерова пути.
]
#proof()[
  1. #list()[
    $==>$ Рассмотрим эйлеров цикл $v_1 e_1 v_2 e_2 dots e_k v_1$. ($v_i$ не обязательно различны)
    Будем идти по пути: степень $v_1$ увеличится на $1$, $v_2$ на $2$, $v_3$ на $2$, $dots$, $v_1$ еще на $1$. Значит $forall i "deg"(v_i) divides 2$.
  ][
    $<==$ Индукция по $m=|E(G)|$. База $m = 0$ --- очевидно. Индукционный переход: верно для $m = 0, 1, dots, m$, то и для $m + 1$. $|E(G)| = m +1$ значит что есть хотя бы одно ребро, жадно ходим по графу. Можем т.к. $forall i "deg"(v_i) divides 2$. Ходим пока не вернемся в $v_1$. Получим цикл $C$ из $v_1$ в $v_1$. Рассмотрим $G' = G - E(C)$. $G' = G_1 union.sq G_2 dots union.sq G_k$, $G_i$ --- связные. $forall i, v in V(G_i) "deg"(v) divides 2$. По индукционному прежположению $forall i$ в  $G_i$ есть эйлеров цикл $C_i$. осталось склеить $C$ и $C_i$.
  ]
  2.
    - $==>$ аналогично
    - $<==$ Добавим ребро $e_1 = v_1 v_2$ в $G$. $G' = G + e_1$. В $G'$ степени всех вершин четны. Применим к $G$ $(1)$. Тогда в $G$ есть эйлеров цикл $v_1 e_1 v_2 dots v_1$. Уберем $v_1 e_1$ из начала, получим эйлеров путь в $G$ и $v_1$ и $v_2$ его начало и конец.
]

== #todo() Графы. Гамильтоновы графы. Определения. Теорема Оре. Примеры использования.
#definition()[
  Простой путь (цикл) называется *гамильтоновым*, если он проходит по всем вершинам.
]
#definition()[
  Граф называется *гамильтоновым* если в нем есть гамильтонов цикл. Аналогично *полугамильтоновым* если нет цикла, но есть путь.
]
#theorem([Оре])[
  $n = |V(G)|$. $G$ --- простой.
  1. Если для любых несмежных $u$ и $v$ $"deg"(u) + "deg"(v) >= n$ $==>$ $G$ --- гамильтонов
  2. Если для любых несмежных $u$ и $v$ $"deg"(u) + "deg"(v) >= n - 1 ==>$ в $G$ найдется гамильтонов путь
] <theorem-ore>

#proof(ref(<theorem-ore>, supplement: [теоремы]))[
  1. Пусть $G$ не гамильтонов. Очевидно что $K_n$ --- гамильтонов. Будем постепенно добавлять ребра в $G$, пока не получится $K_n$. Получается в какой-то момент получим гамилтонов граф и все дальнейшие тоже будут гамильтоновыми. Пусть $G_k$ --- не гамильтонов, а $G_(k + 1)  + e$ --- гамильтонов. Рассмотрим $G_k$.
    1. В нем есть гамильтонов путь, т.к. в $G_(k + 1)$ есть гамильтонов цикл
    2. Для $G_k$ верно, что любые несмежные $u$ и $v$ $"deg"(u) + "deg"(v) >= n$ --- это было верно в $G$, а $G_k$ получен из $G$ добавлением ребер. Рассмотрим гамильтонов путь в $G_k$. $v_1$ и $v_n$ несмежны $==> "deg"(v_1) + "deg"(v_n) >= n$
      #align(center)[
        #let scale = 0.5
        #diagram(debug: 0, {
          node((0, 0),  [$v_1$], fill:black, radius: 2pt, name: <1>)
          node((scale * 1, scale * 1),  [$v_2$], fill:black, radius: 2pt, name: <2>)
          node((scale * 2, scale * 0),  none, fill:black, radius: 2pt, name: <3>)
          node((scale * 3, scale * 1),  [$v_l$], fill:black, radius: 2pt, name: <4>)
          node((scale * 4, scale * 0),  move(dy: -18pt, dx: 12pt)[$v_(l +1)$], fill:black, radius: 2pt, name: <5>)
          node((scale * 5, scale * 1),  none, fill:black, radius: 2pt, name: <6>)
          node((scale * 6, scale * 0),  none, fill:black, radius: 2pt, name: <7>)
          node((scale * 7, scale * 1),  move(dx: 5pt)[$v_n$], fill:black, radius: 2pt, name: <8>)

          edge(<1>, <2>)
          edge(<2>, <3>)
          edge(<3>, <4>)
          edge(<4>, <5>)
          edge(<5>, <6>)
          edge(<6>, <7>)
          edge(<7>, <8>)

          edge(<1>, <5>, bend: 50deg, stroke: red, dash: "dashed")
          edge(<4>, <8>, bend: -50deg, stroke: red, dash: "dashed")
        })
      ]
      Будем ставить + если из $v_1$ есть ребро в правую вершину пары. Будем ставить - если из $v_n$ есть ребро в левую вершину пары. Суммарно поставим хотя бы $n$ значков (т.к. $"deg"(v_1) + "deg"(v_n) >= n$). По принципу Дирихле у какой-то пары стоит и + и -. Т.е. $v_l v_(l + 1)$: есть ребро $v_1 v_(l + 1)$ и ребро $v_n v_l$. Но тогда существует гамильтонов цикл $v_1 v_(l + 1) v_(l + 2) dots v_n v_l v_(l - 1) dots v_1$. Противоречие.
  2. Рассмотрим $G' = G + v_1$. Соединим $v_1$ со всеми вершинами графа $G$. Пусть $u$ и $v$ несмежные вершины $G'$ (они же несмежны в $G$). В $G'$ $"deg"(u) + "deg"(v) >= n + 1$ и $|V(G')| = n + 1$ $==>^#text[(1)]$ $G'$ --- гамильтонов. Удалим из гамильтонова цикла графа $G'$ вершину $v_1$, получим гамильтонов путь графа $G$.
]

== #todo() Графы. Гамильтоновы графы. Определения. Необходимое условие. Теорема Дирака (как следствие теоремы Оре). Примеры использования.
#theorem([Дирака])[
  $n = |V(G)|$. $G$ --- простой.
  1. Если $forall v in V(G) med "deg"(v) >= n /2 ==> G$ --- гамильтонов
  2. Если $forall v in V(G) med "deg"(v) >= (n - 1) / 2 ==>$ в $G$ найдется гамильтонов путь
]

#proof([Оре $==>$ Дирак])[
  Если $forall v : "deg"(v) >= n / 2 ==> forall u, v med "deg"(u) + "deg"(v) >= n$ $==>^#text[т. Оре]$ $G$ --- гамильтонов.
]

#remark()[
  $G$ --- орграф. Для любых несмежных $u$ и $v$ (из $u$ нет $->$ в $v$) $"outdeg"(u) + "indeg"(v) >= n ==> G$ --- гамильтонов.
]
== Графы. Паросочетания. Определения и примеры. Теорема Бержа.
#definition()[
  $M subset E(G)$ называется *паросочетанием* если $forall e_1, e_2 in M ==> $ $e_1$ и $e_2$ не смежны.
]

#definition()[
  Паросочетание называется *наибольшим* по включению если оно не содержится ни в каком другом паросочетании.
]

#definition()[
  Паросочетание $M$ называется *максимальным* если для любого $M'$ --- паросочетание, $|M'| <= |M|$.
]

#symb()[
  Мощность максимального паросочетания обозначают $alpha'(G)$.
]

#definition()[
  $G$, $M$ --- паросочетание $G$, $l$ --- путь в $G$. $l = v_1 e_1 v_2 e_2 v_3 dots e_k v_(k + 1)$, $v_1 != v_(k + 1)$, $l$ называется $M$-чередующимся, если $cases(e_(2k) in M, e_(2k + 1) in.not M)$ или $cases(e_(2k + 1) in M, e_(2k) in.not M)$
]

#definition()[
  Пусть $l$ --- $M$-чередующийся путь графа $G$. Если $v_k$ и $v_(k + 1)$ не покрыты $M$ (во всем $G$), то $l$ называется *$M$-дополняющим* путем.
]

#theorem([Бержа])[
  $M$ --- максимальное паросочетание $<==>$ в $G$ отсутствуют $M$-дополняющие пути.
]
#proof()[
  - $==>$ очевидно
  - $<==$ Пусть не так, тогда $exists M'$ --- паросочетание: $|M'| > |M|$. Рассмотрим $G' = angle.l V(G), M' triangle M angle.r$. $forall v in V(G') : "deg"(v) <= 2$ ($0$ если покрывалось обоими, $1$ если ровно одним, $2$ если ни одним).
    $G'$ --- совокупность бамбуков и циклов четной длины. Существует бамбук, в нем чередуются ребра из $M$ и $M'$ причем первое и последнее ребро из $M'$. Нашли $M$-дополняющий путь в $G$. Противоречие.
]

#definition()[
  $B subset V(G)$ называется *вершинным покрытием*, если $forall e in E(G)$ инцидентно хотя бы одной вершине из $B$.
]

#definition()[
  Вершинное покрытие $B$ называется *минимальным*, если $forall B'$ --- вершинное покрытие $|B'| >= |B|$.
]

#symb()[
  Размер минимального вершинного покрытие --- $beta(G)$.
]

#remark()[
  - $alpha$ --- про максимум, $beta$ --- про минимум
  - Если есть $'$ --- про ребра, нет --- про вершины
  Пример:
  - $beta'$ --- минимальное реберное покрытие.
]

#lemma([О слабой двойственности])[
  $forall G: alpha'(G) <= beta(G)$
]
#proof()[
  Пусть $M$ --- максимальное паросочетание. $(|M| = alpha'(G))$. Т.к. не существует вершины покрывающей сразу $2$ ребра из $M$, то для покрытия нужно хотя бы $|M|$ вершин
]

#remark()[
  Если нашли минимальное вершинное покрытие $B$ и максимальное паросочетание $M'$, такие что $|B| = |M'| = n$:
  $ n = |M'| <- alpha'(G) <= beta(G) <= |B| = n ==> alpha'(G) = beta(G) = n $
]

#remark()[
  Есть теорема о сильной двойственности в двудольном графе.
]

#definition()[
  Паросочетание которое покрывает все вершины называется *совершенным*.
]
== #todo() Графы. Паросочетания. Лемма Холла. Примеры использования.
#symb[$G[X, Y]$ --- двудольный граф с долями $X$, $Y$]

#definition()[
  Если паросочетание $M$ покрывает все вершины $X$ графа $G[X, Y]$, то такое паросочетание называется *$X$-насыщенным*
]

#definition()[
  - $N(v) = {u : u #text[смежно с $v$]}$ 
  - $N(U) = {u in.not U : exists v in U : u in N(v) }$
]

#theorem([Холла])[
  В $G[X, Y]$ существует $X$-насыщенное паросочетание $<==>$ $forall U subset X : |U| <= |N(U)|$ (условие Холла).
]
#proof()[
  - $==>$ очевидно
  - $<==$ $n = |X|$. Индукция по $n$. База: $n = 1$. Индукционный переход $1,2,dots,n mapsto n + 1$.
  #enum(numbering: "I.")[
    $exists X' subset X : X' != emptyset and X' != X : |X'| = |N(X')|$. 
    1. Рассмотрим $G'[X', N(X')]$ --- для $G'$ выполняется условие Холла. Тогда по ИП $exists M'$ --- $X'$-насыщенное паросочетание.
    2. Рассмотрим $G''[X \\ X', Y \\ N(X')]$. Докажем что условие Холла выполнено. Пусть не так, т.е. $exists U subset X \\ X' : |N_(G'')(U)| <= |U|$. Рассмотрим $X' union U$:
    $ |N_G (X')| + |N_(G'')(U)| <  |X'| + |U| = |X' union U| <= N_G (X' union U) + |N_G (X')| + N_(G'')(U) $
    Противоречие. Значит для $G''$ условие Холла выполняется. Значит $exists M''$ --- $(X \\ X')$-насыщенным паросочетанием.
  Тогда $M = M' union M''$ является $X$-насыщенным паросочетанием
  ][
    $forall X' subset X: X' != emptyset and X' != X : |X'| < |N(X')|$

    $x in X, y in N(x)$. Рассмотрим $hat(G)[X \\ x, Y \\ y]$. Проверим что для $hat(G)$ выполняется условие Холла. $U subset X \\ x$, проверим что $|U| <= |N_(hat(G))(U)|$.
    $ |U| < |N_G (U)| ==> |U| <= |N_G (U)| - 1 <= |N_(hat(G))(U)| $
    Значит $exists M'$ --- $(X \\ x)$-насыщенным паросочетанием $==>$ $M = M' union (x y)$ является $X$-насыщенным паросочетание в $G$.
  ]
]
