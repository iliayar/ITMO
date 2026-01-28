#import "../../../../other/typst/lecture_mse.typ": *

#show: doc => lecture(
  subj: [Функциональне программирование],
  title: [Вопросы к экзамену],
  date: [27 января],
  number: 0,
  program: "ITMO MSE y2025",
  doc
)

#let betastep = $scripts(~>)_beta$
#let betasteps = $scripts(->>)_beta$
#let betaeq = $scripts(=)_beta$
#let alphastep = $scripts(~>)_alpha$
#let alphaeq = $scripts(=)_alpha$
#let etastep = $scripts(~>)_eta$
#let betaetaeq = $scripts(=)_(beta eta)$
#let parbetastep = $scripts(=>)_(beta)$

= Теория
== Сравнение функционального и императивного подходов к программированию. Функциональная модель вычислений.
- Императивная модель (Sequential Model of Computation). Программа это последовательность инструкций, изменяющих состояние
  + Последовательные инструкции
  + Изменяем состояние
  + Условия и циклы
  + Завершается после последней инструкции
- Функциональная модель. Программа это выражение. Ее исполнение это редукция (вычисление) этого выражения
  + Вычисляются редексы по заданым правилам
  + Завершается когда не осталось редексов
  + `=` это связывание. Рекурсивное связывание

#remark()[
  Что-то про
  - Разные стратегии редукции: строгий (правый терм аппликации вычисляется до не редекса), ленивая (самый левый внешний редекс).
  - Что-то про каррирование.
]
== Чистое $lambda$-исчисление. $lambda$-термы, свободные и связанные переменные. Классические комбинаторы, комбинаторная логика.
#definition()[
  Множество лямбда термов $V = {x, y, z, dots}$
  $ x in V & ==> x in Lambda \
    M, N in Lambda & ==> (M med N) in Lambda \
    M in Lambda, x in V & ==> (lambda x.med M) in Lambda
  $
  Или
  $ Lambda ::= V | (Lambda med Lambda) | (lambda V.med Lambda) $
]

#remark()[ Про приоритеты и ассоциативность ]

#definition[
  $beta$-редукция
  $ (lambda x.med M) med N betastep [x |-> N] M $
]

#definition[
  Множество $"FV"(T)$ *свободных* переменных в терме $T$:
  $ "FV"(x) & = {x} \
    "FV"(M med N) & = "FV" (M) union "FV" (N) \
    "FV" (lambda x.med M) & = "FV" (M) \\ {x}
  $
]

#definition[
  Множество $"BV"(T)$ *связанных* переменных в терме $T$:
  $ "BV"(x) & = emptyset \
    "BV"(M med N) & = "FV" (M) union "FV" (N) \
    "BV" (lambda x.med M) & = "BV" (M) union {x}
  $
]
#definition[ $(lambda x.med M) med N$ --- $beta$-редекс ]

#definition[ $M$ --- *замкнутый терм* если $"FV"(M) = emptyset$ ]

#definition[
  $ bold(I) & = lambda x. med x \
    bold(omega) & = lambda x. med x med x \
    bold(Omega) & = bold(omega) med bold(omega) = (lambda x.med x med x) med (lambda x.med x med x) \
    bold(K) & = lambda x med y .med x \
    bold(K_*) & = lambda x med y .med y \
    bold(C) & = lambda f med x med y .med f med y med x \
    bold(B) & = lambda f med g med x .med f med (g med x) \
    bold(S) & = lambda f med g med x .med f med x med (g med x)
  $
]

#remark[ Про переименование связных перменных ]
#definition[ Термы *$alpha$-эквивалентны* если отличаются только именами связных переменных ]

#remark[ Комбинаторы можно определить как примитив. $bold(S), bold(K)$ --- базис ]
== Подстановка, лемма подстановки. Одношаговая и многошаговая $beta$-редукция, $beta$-эквивалентность.
#remark[
  Подстановка $[x |-> A]M$ заменяет только свободные $x$. Есть соглашение (Барендрегта) что имена связаных всегда выбираем так чтобы они отличались от имен свободных.
]
#definition[
  *Подстановка* определена индуктивно:
  $ & [x |-> N] x && = N \
    & [x |-> N] y && = y \
    & [x |-> N] (P med Q) && = ([x |-> N)P) med ([x |-> N] Q) \
    & [x |-> N] (lambda x.med P) && = lambda x.med P \
    & [x |-> N] (lambda y.med P) && = lambda y.med [x |-> N] P &&& #[если $y in.not "FV"(N)$] \
    & [x |-> N] (lambda y.med P) && = lambda y'.med [x |-> N] ([y |-> y']P) &&& #[если $y in "FV"(N)$]
  $
]

#remark[ Подстановки не коммутируют. Т.е. $[x |-> N]([y |-> L]M)$ не обязательно равно $[y |-> L]([x |-> N]M)$ ]
#lemma[
  Пусть $M, N, L in Lambda$. Предположим $x equiv.not y$ и $x in.not "FV"(L)$. Тогда
  $ [y |-> L] ([x |-> N] M) equiv [x |-> [y |-> L]N]([y |-> L]M) $
]
#proof[ Индукция по всем случаям ]

#definition[
  Бинарное отношение $cal(R)$ над $Lambda$ *совместимое* если $forall M, N, Z in Lambda med forall x in V$
  $ M med cal(R) med N => Z med M med cal(R) med Z med N \
    M med cal(R) med N => M med Z med cal(R) med N med Z \
    M med cal(R) med N => lambda x.med M med cal(R) med lambda x.med N
  $
]

#definition[
  Наименьшее совместимое отношение $betastep$ содержащее правило $beta$:
  $ (lambda x.med M) med N betastep [x |-> N] M $
  называется *отношением $beta$-редукции*
]

#definition[
  Бинарное отношение $betasteps$ над $Lambda$
  $ & M betasteps M && #[(refl)] \
    M betastep N => & M betasteps N && #[(ini)] \
    M betasteps N, N betasteps L => & M betasteps L && #[(trans)]
  $
  Транзитивное рефлексивное замыкание $betastep$
]

#remark[ $betasteps^+$ --- транзитивное замыкание $betastep$ ]

#definition[
  Бинарное отношение $beta$-конвертируемости $betaeq$ над $Lambda$
  $ M betasteps N & => M betaeq N && #[(ini)] \
    M betaeq N & => N betaeq M && #[(sym)] \
    M betaeq N, N betaeq L & => M betaeq L && #[(trans)]
  $
]

#statement[
  Отношение $beta$-конвертируемости является наименьшим отношением эквивалентности, содержащим $beta$-правило
]
#proof[ Индукция по определениям ]

== $alpha$-эквивалентность. Индексы Де Брауна. $eta$-эквивалентность и принцип экстенсиональности.
#definition[
  $lambda x.med M alphastep lambda y.med [x |-> y] M$, если $y in.not "FV"(M)$
]

#remark[ Про De Brujin. $lambda x. med (lambda y.med x med y) <-> lambda med (lambda med 1  med 0)$ ]

#definition[
  Отношение *$eta$-эквивалентности*
  $ lambda x.med M med x etastep M $
  если $x in.not "FV"(M)$
]

#remark[ 
  Можно определить совместимое, рефлексивное, симметричное и транизитивное отношение $eta$-эквивалентности.
  Его смысл в том что вычислительное поведение термов с обоих сторон одинаво:
  $ (lambda x. med N med x) M betaeq N med M $
]

#remark[
  $eta$-преобразование обеспечивает *принцип экстенсиональности*. $forall N : F med N betaeq G med N$

  Выбираем $y in.not "FV"(F) union "FV"(G)$
  $ F med y & betaeq G med y \
    lambda y.med F med y & betaeq lambda y.med G med y #[(правило $xi$)] \
    F & betaetaeq G
  $
]
== Кодирование булевых значений, кортежей в чистом бестиповом $lambda$-исчислении.
#definition[
  $ bold("pair") & := lambda x med y med f .med f x y \
    bold("fst") & := lambda p .med p med lambda x med y.med x = lambda p .med p med bold(K) \
    bold("snd") & := lambda p .med p med lambda x med y.med y = lambda p .med p med bold(K_*) \
  $
  Законы пар
  $ forall N med M med bold("fst") med (bold("pair") med N med M) betaeq N \
    forall N med M med bold("snd") med (bold("pair") med N med M) betaeq M \
  $
]

#definition[
  $ bold("true") & := lambda x med y .med x \
    bold("false") & := lambda x med y .med y \
    bold("if") & := lambda b med x med y .med b med x med y betaetaeq lambda b.med b
  $

  Законы
  $ forall N med M med bold("if") med bold("true") med N med M betaeq N \
    forall N med M med bold("if") med bold("false") med N med M betaeq M
  $
]

== Кодирование чисел Чёрча в чистом бестиповом $lambda$-исчислении. Арифметические операции над ними.
#definition[
  $ bold(0) := lambda f med z .med z \
    bold("suc") := lambda n med f med z .med f med (n med f med z)
  $
  Законы
  $ bold("natElim") med overline(n) med f med z betaeq underbrace(f med "("f med dots med "("f, n) med z")"")" #fixme() \
    forall f med "ini" med bold("natElim") med bold(0) med f med "init" betaeq "ini" \
    forall n med f med "ini" med bold("natElim") med (bold("suc") med n) med f med "ini" betaeq f med (bold("natElim") med n med f med "ini")
  $
]

#statement[
  Операции #todo()
]
== Теорема о неподвижной точке. $Y$-комбинатор. Решение рекурсивных уравнений на термы.
#theorem([О неподвижной точке])[
  Для любого $lambda$-терма $F$ существует неподвижная точка. $forall F in Lambda med exists X in Lambda med F med X betaeq X$.
]
#proof[
  Введем $W := lambda x.med F med (x med x)$ и $X := W med W$. Тогда
  $ X equiv W med W equiv (lambda x.med F med (x med x)) med W betaeq F med (W med W) equiv F med X $
]

#theorem([О комбинаторе неподвижной точки])[
  Существует $bold(Y)$, такой что $forall F in Lambda med F med (bold(Y) med F) betaeq bold(Y) med F$
]
#proof[
  Введем $bold(Y) := lambda f.med (lambda x.med f med (x med x)) med (lambda x.med f med (x med x))$. Заметим что $bold(Y) F betaeq W med W$. Тогда из предыдщуего доказательства:
  $ bold(Y) med F betaeq W med W betaeq F med (W med W) equiv F med (bold(Y) med F) $
]

#remark[
  Как решать рекурсивные уравнения с помощью этого:
  $ F med N = N med F \
    F med N = (lambda f med n.med n med f) med F med N \
    F = undershell((lambda f med n. med n med f), F') F \
    F = bold(Y) med F'
  $
]
== Нормальная форма. Редукционные графы.
#definition[
  $lambda$-терм _находится_ в *$beta$-нормальной форме* ($beta$-NF) если в нем нет подтермов, являющихся $beta$-редексами
]
#definition[
  $lambda$-терм _имеет_ *$beta$-нормальную форму* ($beta$-NF) если для некоторого $N$ выполняется $M betaeq N$ и $N$ находится в $beta$-NF
]

#statement[
  Не все термы имеют $beta$-NF
]
#example[
  $bold(Omega) equiv bold(omega) med bold(omega) betastep bold(omega) med bold(omega)$
  Но это не значит что $bold(Omega)$ не имеет нормальную форму. Можем существовать какой-то $M$ и $N$ в $beta$-NF, такой что
  #align(center, diagram(spacing: 0.5em, $
    "" & edge("dl", ->>) M edge("dr", ->>) & "" \
    bold(Omega) & "" & N
  $))
  Тогда $bold(Omega) betaeq N$
]

#definition[
  *Редукционный граф* терма $M in Lambda$ (обозначаемый $G_beta (M)$) --- это ориентированный мультиграф с вершинами в ${N | M betasteps N}$ и дугами $betastep$.
]
#example[
  $ G_beta (bold(I) med (bold(I) med x)) = #move(dy: -0.5pt, diagram({
      node((0, 0), none, fill: black, radius: 2pt, name: <1>)
      node((1, 0), none, fill: black, radius: 2pt, name: <2>)
      node((2, 0), none, fill: blue, radius: 2pt, name: <3>)

      edge(<1>, <2>, "->", bend: 45deg)
      edge(<1>, <2>, "->", bend: -45deg)
      edge(<2>, <3>, "->")
    }))
  $

  $ G_beta ((lambda x.med x med bold(I)) med bold(Omega)) = #move(dy: -6pt, diagram({
      node((0, 0), none, fill: black, radius: 2pt, name: <1>)
      node((1, 0), none, fill: blue, radius: 2pt, name: <2>)

      edge(<1>, <1>, "->", bend: 165deg, loop-angle: 90deg)
      edge(<1>, <2>, "->")
    }))
  $
]
== Теорема Чёрча-Россера. Параллельная $beta$-редукция. Полная эволюция.
#theorem([Черча-Россера])[
  Если $M betasteps N, M betasteps K$, то существует $L$, такой что $N betasteps L$ и $K betasteps L$.
]
#remark[
  $beta$-редукция обладает *свойством ромба*
  #align(center, diagram(spacing: 1em, $
    "" & edge("bl", ->>) M edge("br", ->>) & "" \
    N edge("br", dash: "dotted", ->>) & "" & edge("bl", dash: "dotted", ->>) K \
    "" & L & ""
  $))
]
#remark[ $betastep$ не обладает этим свойством ]

#definition[
  Бинарное отношение *параллельной $beta$-редукции* 
  - $x parbetastep x$ для любой переменной $x$
  - если $P parbetastep P'$, то $lambda x.med P parbetastep lambda x.med P'$
  - если $P parbetastep P'$ и $Q parbetastep Q'$, то $P med Q parbetastep P' med Q'$
  - если $P parbetastep P'$ и $Q parbetastep Q'$, то $(lambda y.med P) med Q parbetastep [y |-> Q']P'$
]
#remark[ Это отношение рефлексивно, но не тразитивно --- можно сокращать только изначально существовавшие редексы ]

#lemma[
  1. Если $M betastep M'$, то $M parbetastep M'$
  2. Если $M parbetastep M'$, то $M betasteps M'$
  3. Если $M parbetastep M'$ и $N parbetastep N'$, то $[x |-> N] M parbetastep [x -> N']M'$
]
#proof[
  1. Индукция по определению $M betastep M'$
  2. Индукция по определению $M parbetastep M'$
  3. Аналогично (2). \
    4 cлучай $M = (lambda y.med P) med Q, M' = [y |-> Q'] P'$. \
    ИП: $[x |-> N] P parbetastep [x |-> N'] P', [x |-> N] Q parbetastep [x |-> N'] Q'$
    $ [x |-> N] M equiv [x |-> N]((lambda y.med P) med Q) = & #h(2em) #text(blue)[определение $|->$] \
      (lambda y.med [x |-> N] P) med ([x |-> N]Q) parbetastep & #h(2em) #text(blue)[ИП + определение $parbetastep$] \
      [y |-> [x |-> N']Q'] ([x |-> N'] P') & #h(2em) #text(blue)[Лемма подстановки] \
      [x |-> N'] ([y |-> Q'] P') equiv [x |-> N'] M'
    $
]

#definition[
  *Полной эволюцией* (complete development) терма $M$ называют терм $M^*$, определяемый индуктивно
  $ x^* & = x \
    (lambda x.med P)^* & = lambda x.med P^* \
    (P med Q)^* & = P^* med Q^* #[если $P$ не абстракция] \
    ((lambda x.med P) med Q)^* & = [x |-> Q^*] P^*
  $
]
#remark[
  Отношение $M parbetastep N$ порождается сокращением _некоторых_ редексов в $M$, а $M^*$ --- сокращением _всех_ редексов
]
#example[ $(bold(omega) med (bold(I) med bold(I)))^* = bold(I) med bold(I)$ ]

#lemma([о полной эволюции])[
  Если $M parbetastep M'$, то $M' parbetastep M^*$.
]
#proof[
  индукция по определению $M parbetastep M'$.
]

#corollary_lemma[
  Если $M parbetastep M'$ и $M parbetastep M''$, то $M' parbetastep M^*$ и $M'' parbetastep M^*$
]
#remark[ Это свойство ромба $parbetastep$ ]

#proof([Черч-Россер])[
  Если $M betastep dots betastep N$ и $M betastep dots betastep K$, то $M parbetastep dots parbetastep N$ и $M parbetastep dots parbetastep K$. Сцепляя диаграмки
  #align(center, diagram(spacing: 1em, $
    "" & "" & edge("bl", =>) M edge("br", =>) & "" & "" & "" \
    "" & edge("bl", =>) circle.small.filled edge("br", =>) & "" & edge("bl", =>) circle.small.filled edge("br", =>) & "" & "" \
    N edge("br", =>) & "" & edge("bl", =>) circle.small.filled edge("br", =>) & "" & edge("bl", =>) circle.small.filled edge("br", =>) & "" \
    "" &circle.small.filled edge("br", =>) & "" & edge("bl", =>) circle.small.filled edge("br", =>) & "" & edge("bl", =>) K \
    "" & "" & circle.small.filled edge("br", =>) & "" & edge("bl", =>) circle.small.filled & "" \
    "" & "" & "" & L & "" & ""
  $))
  находим $L$, такое что $N parbetastep dots parbetastep L$ и $K parbetastep dots parbetastep L$ откуда $N betasteps dots betasteps L$ и $K betasteps dots betasteps L$
]
== Следствия теоремы Чёрча-Россера.
#corollary[
  Если $M betaeq N$, то существует $L$, такой что, $M betasteps L$ и $N betasteps L$.
]
#proof[
  Индукция по генерации $betaeq$
  - $M betaeq N$, поскольку $M betasteps N$. Возьмем $L equiv N$
  - $M betaeq N$, поскольку $N betaeq M$. По ИП имеется общий $beta$-редукт $L_1$ для $N, M$. Возьмем $L equiv L_1$
  - $M betaeq N$, поскольку $M betaeq N', N' betaeq N$. Тогда
  #align(center, diagram(spacing: 1em, $
    M edge("br", ->>) & #[(ИП)] & edge("bl", ->>) N' edge("br", ->>) & #[(ИП)] & edge("bl", ->>) N \
    "" & L_1 edge("br", ->>, dash: "dotted") & #[Черч-Россер] & edge("bl", ->>, dash: "dotted") L_2 & "" \
    "" & "" & L & "" & ""
  $))
]

#theorem([Редуцируемость к NF])[
  Если $M$ имеет $N$ в качестве $beta$-NF, то $M betasteps N$
]
#remark[
  Теперь можно доказать что у $bold(Omega)$ нет нормальной формы. Тогда должо было бы выполняться $bold(Omega) betasteps N$, но $bold(Omega)$ редуцируется лишь к себе и не является нормальной формы
]

#theorem([Единственность NF])[
  $lambda$-терм имеет не более одной $beta$-NF
]
== Cтратегии редукции. Теорема о нормализации. Механизмы вызова в функциональных языках.
#definition[
  Терм *слабо нормализуем* ($"WN"_beta$) если _существует_ последовательность $beta$-редукций приводящих его к $beta$-NF.
]
#definition[
  Терм *сильно нормализуем* ($"SN"_beta$) если любая последовательность $beta$-редукций приводит его в $beta$-NF
]

#theorem[
  $lambda$-терм можем иметь одну из двух форм.
  $ lambda arrow(x).med y med arrow(N) equiv lambda x_1 med dots med x_n.med y med N_1 med dots med N_k quad n>= 0, k >= 0 \
    lambda arrow(x).med (lambda z.med M) med arrow(N) equiv lambda x_1 med dots med x_n.med (lambda z.med M) med N_1 med dots med N_k quad n>= 0, k > 0
  $
]
#definition[
 Первая форма называется *головная норамальная форма* (HNF): переменная $y$ называется *головной переменной*, а редекс $(lambda z.med M) med N_1$ --- *головным редексом*. Переменная $y$ можем совпадать с одной из $x_i$
]

#definition[
  *Слабая головная нормальная форма* (WHNF) --- это HNF или лямбда-абстракция, то есть не редекс на верхнем уровне.
]

#definition[
  Стратегия редукции $F$ --- это отображение множества $Lambda$ в себя, тождественное для нормальных форм и обладающее свойством $M betastep F(M)$ для прочих термов.
]

#definition[
  Нормальная (крайне левая) стратегия $F_1$:
  $ F_1(lambda arrow(x).med y med arrow(P) med Q med arrow(R)) & = lambda arrow(x).med y med arrow(P) med F_1(Q) med arrow(R) quad #text[если $arrow(P) in "NF"_beta" "$ и $" "Q in.not "NF"_beta$] \
    F_1(lambda arrow(x).med (lambda z.med M) med Q med arrow(R)) & = lambda arrow(x).med [z |-> Q]M med arrow(R)
  $
]

#definition[
 Аппликативная стратегия стратегия $F_a$:
  $ F_a (lambda arrow(x).med y med arrow(P) med Q med arrow(R)) & = lambda arrow(x).med y med arrow(P) med F_a (Q) med arrow(R) quad #text[если $arrow(P) in "NF"_beta" "$ и $" "Q in.not "NF"_beta$] \
    F_a (lambda arrow(x).med (lambda z.med M) med Q med arrow(R)) & = lambda arrow(x).med [z |-> Q]M med arrow(R) quad #text[если $Q in "NF"_beta$] \
    F_a (lambda arrow(x).med (lambda z.med M) med Q med arrow(R)) & = lambda arrow(x).med (lambda z.med M) med F_a (Q) med arrow(R) quad #text[если $Q in.not "NF"_beta$]
  $
]

#definition[
  Стратегия редукции называется _нормализующей_ если для любого $M in "WN"_beta$ существует конечное $i in NN$ такое что $F^i (M) in "NF"_beta$
]

#statement[
  Аппликативная стратегий не нормализующая
]
#example[
  $bold(K) med bold(I) med bold(Omega)$. У него есть нормальная форма $bold(I)$. Однако аппликативная стратегия "зависнет" на вычислении $bold(Omega)$.
]

#theorem([о нормализации])[
  Нормальная стратегия $F_1$ является нормализующей
]

#remark[
  Теперь можем доказать отсутсвие $"NF"_beta$ у терма. Например, $bold(K) med bold(Omega) med bold(I)$.

  Попробуем проредуцировать нормальной стратегией:
  $ bold(K) med bold(Omega) med bold(I) betasteps bold(Omega) betastep bold(Omega) betastep dots $
  Понятно что не существует $i in NN$ такого что $F_1 (bold(K) med bold(Omega) med bold(I))$ будет в нормальной форме. А т.к. $F_1$ нормализуема, то получается что у терма нет нормальной формы вообще. #fixme()
]

#remark[
  - Нормальная стратегия можем быть неэффективна: один и тот же терм придется считать несколько рах
  - Нормальная стратения ленивая
]
== Функция предшествования для чисел Чёрча. Комбинатор примитивной рекурсии.
#remark[
  Цикл по интревалу:
  ```python
  def rec(f, ini, n):
    state = ini
    for i in range(0, n):
      state = f(i, state)
    return state
  ```
]
#definition[
  $ bold("rec") med f med "ini" med n betaeq f med (n - 1) med (f med (n - 2) med (dots (f med 1 med (f med 0 med "ini")) dots )) $
  Как это сделать:
  $
    bold("start") med "ini" := bold("pair") med bold(0) med "ini" \
    bold("step") med f med (bold("pair") med i med "res") := bold("pair") med (bold("suc") med i) med (f med i med "res") \
    bold("iter") med f med "ini" med n := bold("natElim") med n med (bold("step") med f) med (bold("start") med "ini") \
    bold("rec") med f med "ini" med n := bold("snd") med (bold("iter") med f med "ini" med n)
  $
]

#remark[
  $bold("pred") med n := bold("rec") med bold(K) med bold(0) med n$
]
== Просто типизированное $lambda$-исчисление в стиле Карри. Предтермы. Утверждения о типизации. Контексты. Правила типизации.
#remark[
  Термы те же что и в бестиповом. Каждый терм обладает множеством различных типов.
]
#definition[
  Множество типов $TT$ системы $lambda_->$ определяется индуктивно
  $ & alpha, beta, dots in TT && #text[(переменные типа)] \
    & A, B in TT ==> (A -> B) in TT && #text[(типы пространства функций)]
  $
  или
  $ TT ::= VV | (TT -> TT) $
  где $VV = {alpha, beta, dots}$
]

#definition[
  Множество *предтермов* (или *псевдотермов*) $Lambda$ строится из переменных из $V = {x, y, z, dots}$ с помощью аппликации и абстракции
  $ x in V & => x in Lambda \
    M, N in Lambda & => (M med N) in Lambda \
    M in Lambda, x in V & => (lambda x.med M) in Lambda
  $
  или
  $ Lambda ::= V | (Lambda med Lambda) | (lambda V.med Lambda) $
]
#remark[ Предтермы это в точность термы $lambda$ ]

#definition[
  *Утверждение* типизации в $lambda_->$ "а ля Карри" имеет вид
  $ M : A $
  где $M in Lambda$ и $A in TT$. Тип $A$ иногда называют *предикатом*, а терм $M$ --- *субъектом* утверждения
] <statement-curry>

#definition[
  *Объявление* --- утверждение типизации с термовой переменной в качестве субъекта
]

#definition[
  *Контекст* --- это множество объявлений с различными переменными в качестве субъекта
  $ Gamma = {x_1^(A_1), dots, x_n^(A_n) } $
]

#remark[
  Можно рассматривать как частичную функцию $V -> TT$
]

#definition[
  Утверждение $M : C$ называется *выводимым* в контексте $Gamma$
  $ Gamma tack M : C $
  если его вывод может быть произведен по правилам
  $ #text[(аксиома)] quad & Gamma tack x : A quad #text[если $x^A in Gamma$] \
    #text[($-> E$)] quad & (Gamma tack M : A -> B quad Gamma tack N : A) / (Gamma tack M med N : B) \
    #text[($-> I$)] quad & (Gamma, x^A tack M : B) / (Gamma tack lambda x.med M : A -> B)
  $
  Если для предтерма $M$ существуют $Gamma$ и $C$ такие что $Gamma tack M : C$, то его называют *(допустимым) термом*
] <rules-curry>
== Просто типизированное $lambda$-исчисление в стиле Чёрча. Предтермы. Утверждения о типизации. Контексты. Правила типизации.
#remark[
  Термы --- аннотированные версии бестиповых термов. Каждый терм имеет тип, выводимый из способа, которым терм аннотирован
]

#definition[
  Множество *предтермов* $Lambda_TT$ строится из переменных из $V = {x, y, z, dots}$ с помощью аппликации и аннотированной типами абстракции:
  $ Lambda_TT ::= V | (Lambda_TT med Lambda_TT) | (lambda V^TT .med Lambda_TT) $
]

#remark[ Утверждение типизации см. #ref(<statement-curry>). Только вместо $Lambda$ --- $Lambda_TT$ ]
#remark[ Правила см. #ref(<rules-curry>). Только в абстракции $x$ аннотирован ]
== Свойства систем просто типизированного $lambda$-исчисления.
#lemma([об инверсии (генерации)])[
  - $Gamma tack x : A => x^A in Gamma$
  - $Gamma tack M med N : B => exists A med Gamma tack M : A -> B and Gamma tack N : A$
  - $Gamma tack lambda x.med M : C => exists A, B med Gamma, x^A tack M : B and C equiv A -> B$
  - $Gamma tack lambda x^A.med M : C => exists B med Gamma, x^A tack M : B and C equiv A -> B$
]
#lemma([о типизируемости подтерма])[
  Пусть $M'$ --- подтерм $M$. Тогда $Gamma tack M : A => Gamma' tack M' : A'$ для некоторых $Gamma'$ и $A'$.
]

#lemma([разбавления (thinning)])[
  Пусть $Gamma, Delta$ --- контексты, причем $Delta supset.eq Gamma$. Тогда $Gamma tack M : A => Delta tack M : A$. Расширение контекста не влияет на выводимость утверждения типизации.
]
#lemma([о свободных переменных])[
  $Gamma tack M : A => "FV"(M) subset.eq "dom"(Gamma)$. Свободные переменные типизированного терма должны присутствовать в контексте
]
#lemma([сужения])[
  $Gamma tack M : A => Gamma arrow.t "FV"(M) tack M : A$. Сужение контекста до множества свободных переменных терма не влияет на выводимость утверждения типизации.
]

#properties[
  Рассмотрим предтерм $x med x$. Предположим что это терм. Тогда имеются $Gamma$ и $B$, такие что
    $ Gamma tack x med x : B $
  По лемме об инверсии существует такой $A$, что правый подтерм $x : A$, а левый подтерм имеет тип $A -> B$.
  По лемме о контекстах $x in "dom"(Gamma)$ и должен иметь там единственное связывание по определению контекста. То есть $A equiv A -> B$ --- тип является подвыражением себя, чего не может быть, поскольку типы конечны.
  По лемме о типизируемости подтерма предтермы $bold(omega), bold(Omega), bold(Y)$ не имеют типа
]
#definition[
  Для типов $A, B in TT$ *подстановку* $A$ вместо пременной типа $alpha$ в $B$ обозначим $[alpha |-> A]B$.
]
#lemma([подстановки типа])[
  - $lambda_->$ Карри. $Gamma tack M : B => [alpha -> A]Gamma tack M : [alpha |-> A]B$
  - $lambda_->$ Черч. $Gamma tack M : B => [alpha -> A]Gamma tack [alpha |-> A]M : [alpha |-> A]B$
]
#lemma([подстановки терма])[
  Пусть $Gamma, x^A tack M : B$ и $Gamma tack N : A$, тогда $Gamma tack [x |-> N]M : B$
]

#theorem([о редукции субъекта])[
  Пусть $M betasteps N$. Тогда $Gamma tack M : A => Gamma tack N : A$.
]
#corollary[
  Множество типизируемых в $lambda_->$ термов замкнуто относительно редукции
]

#theorem([о единственности типа $lambda_->$ а ля Черч])[
  Пусть $Gamma tack_C M : A$ и $Gamma tack_C M : B$. Тогда $A equiv B$
]
#corollary[
  Пусть $Gamma tack_C M : A, Gamma tack_C N : B$ и $M betaeq N$. Тогда $A equiv B$.
]
== Связь между системами Карри и Чёрча. Проблемы разрешимости. Сильная и слабая нормализация.
Зададим на термых стирающее отображение $|dot| : Lambda_TT -> Lambda$
$ |x| & = x \
  |M med N| & = |M| med |N| \
  |lambda x^A.med M| & = lambda x.med |M|
$
Все атрибутированные типами термы из версии Черча $lambda_->$ "проектируются" в термы в версии Карри. 
$ M in Lambda_TT and Gamma tack_C M : A => Gamma tack_C |M| : A $
Термы из версии Карри $lambda_->$ могут быть "подняты" в термы из версии Черча
$ M in Lambda and Gamma tack_C M : A => exists N in Lambda_TT med Gamma tack_C N : A and |N| equiv M $
Для произвольного типа $A in TT$ выполняется
$ A#text[ обитаем в ] lambda_-> #text[ Карри ] <==> A#text[ обитаем в ]lambda_->#text[ Черч] $

#remark[
  Проблемы:
  - $tack M : A?$ Задача проверки типа (Type Checking)
  - $tack M : ?$ Задача синтеза типа (Type Synthesis)
  - $tack ? : A$ Задача обитаемости типа (Type Inhabitation)
]

#definition[
  Систему типов называют *слабо нормализуемой*, если все ее допустимые термы слабо нормализуемы
]
#definition[
  Систему типов называют *сильно нормализуемой*, если все ее допустимые термы сильно нормализуемы
]
#theorem[
  Обе системы $lambda_->$ сильно нормализуемы
]
== Правило `foldr`/`build` и реализация высокоуровневых оптимизаций в GHC.
Операция противоположная `fold` это
```hs
unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr g init = todo
```

Другой способ сделать развертку
```hs
build :: (forall b. (a -> b -> b)-> b -> b) -> [a]
build g = g (:) []
```

Делаем списки на функциях
```
> g c n = c 'H' (c 'i' c '!' n))
> build g
"Hi!"
```

Если отсутствуют вызовы `seq`, то имеем место
$ #[`foldr f z (build g)`] equiv #[`g f z`] $
```hs
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr c n [] = n
foldr c n (x : xs) = x `c` (foldr c n xs)
```

Можем выражать высокоуровневые оптимизации:
```hs
iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

iterateFB :: (a -> b -> b) -> (a -> a) -> a -> b
iterateFB c f y = go y where go x = x `c` go (f x)

{-# RULES
"iterate"   [~1] forall f x. iterate f x = build (\c _ -> iterateFB c f x)
"fold/build"     forall k z g. foldr k z (build g) = g k z
"iterateFB" [1] iterateFB (:) = iterate
#-}
{-# INLINE [1] build #-}
```

- Сначала заменяем вызовы `iterate` на вызов `build`
- Если были вызовы формата `foldr k z (iterate f x)`. То после предыдущего пункта они стали `foldr k z (build (\c _ -> iterateFB c f x))`. Вторым правило заменим вызов `foldr` на прямой вызов нашей лямбды: `(\c _ -> iterateFB c f x) k z`.
- Заменим оставшиеся вызовы `iterateFB` для построения списка обратно на `iterate`.
Таким образом избавились от построения промежуточных списков.
#fixme()
== Понятие главного (наиболее общего) типа. Подстановки типа и их композиция. Унификаторы.
#definition[
  В версии Карри терму можно приписать множество типов. Тип называется *главным (principal)* если из него можно получить любой другой через подстановку.
]

#definition[
  *Подстановка типа* это операция $S : TT -> TT$ такая что
  $ S(A -> B) equiv S(A) -> S(B) $
]
#remark[
  Обчыно подстановка тождественна на всех переменных кроме конечного носителя $"sup"(S) = {alpha | S(alpha) != alpha}$.
]

#lemma([подстановки])[
  Для $alpha_1 != alpha_2$ и $alpha_1 in.not "FV"(A_2)$ верно равенство
  $ [ alpha_2 := A_2 ] ([ alpha_1 := A_1 ]B) equiv [alpha_1 := [alpha_2 := A_2] A_1 ]( [alpha_2 := A_2] B) $
]

#definition[
  *Композиция двух подстановок* --- подстановка с носителем, являющимся объединением их носителей, над которым последовательно выполнены обе подстановки
]
#example[
  - $S = [alpha := gamma -> beta, beta := alpha -> gamma]$
  - $T = [alpha := beta -> gamma, gamma := beta]$
  $ T compose S & = [alpha := T(S(alpha)), beta := T(S(beta)), gamma := T(S(gamma))] \
                & = [alpha := beta -> beta, beta := (beta -> gamma) -> beta, gamma := beta]
  $
]

#statement[
  Подстановки образуют моноид относительно $compose$ с $[]$ в роли нейтрального элемента
]

#lemma([о композиции подстановок])[
  Если подстановка определена как композиция элементарных
  $ [alpha_1 := Alpha'_1, dots, alpha_n := Alpha'_n] equiv [alpha_n := Alpha_n] compose dots compose [alpha_1 := Alpha_1] $
  причем $forall i <= j med alpha_i in.not "FV"(Alpha_j)$, то
  $ forall i,j med alpha_i in.not "FV"(Alpha'_j) $
]
#proof[ Индукция с использованием Леммы подстановки ]

#definition[
  *Унификатор* для типов $Alpha$ и $Beta$ это подстановка $S$, такая что $S(A) equiv S(B)$.
]
#definition[
  $S$ это *главный унификатор* для $Alpha$ и $Beta$, если для любого другого унификатора $S'$ существует подстановка $T$, такая что $S' equiv T compose S$.
]
== Алгоритм унификации.
#theorem[
  Существует алгоритм унификации $U$, который для заданных типов $Alpha$ и $Beta$ возвращает:
  - Главный унификатор $S$ для $Alpha$ и $Beta$, если $Alpha$ и $Beta$ могут быть унифицированы
  - Сообщение об ошибке в противно случае
]

Алгоритм унификации $U$:
$ & U(alpha, alpha) && = [] \
  & U(alpha, Beta) | alpha in "FV"(Beta) && = #[ошибка] \
  & U(alpha, Beta) | alpha in.not "FV"(Beta) && = [alpha := Beta] \
  & U(Alpha_1 -> Alpha_2, alpha) && = U(alpha, Alpha_1 -> Alpha_2) \
  & U(Alpha_1 -> Alpha_2, Beta_1 -> Beta_2) && = U(U_2 Alpha_1, U_2 Beta_1) compose U_2#text[, где ]U_2 = U(Alpha_2, Beta_2)
$
== Алгоритм построения системы ограничений для типизации терма.
#example[
  $ lambda x^#text(blue)[$alpha$] med y^#text(blue)[$beta$] .med underbrace(y^#text(blue)[$beta$] med (lambda z^#text(blue)[$gamma$] .med overbrace(y^#text(blue)[$beta$] med x^#text(blue)[$alpha$], #text(red)[$delta$])), #text(red)[$epsilon$]) $
  1. Припишем типовую (мета-)переменную всем термовым переменным $x^#text(blue)[$alpha$], y^#text(blue)[$beta$]$
  2. Припишем типовую (мета-)переменную всем аппликативным подтермам $(y med x) : #text(red)[$delta$]$
  3. Выпишем уравнения (ограничения) на типы, необходимые для типизируемости терма: $beta ~ alpha -> delta$, $beta ~ (gamma -> delta) -> epsilon$
  4. Найдем главный унификатор для типовых переменных, дающий решения уравнений:
    $ alpha := gamma -> delta, beta := (gamma -> delta) -> epsilon, delta := epsilon $
  Главный тип $lambda x med y .med y med (lambda z.med y med x) : (gamma -> epsilon) -> ((gamma -> epsilon) -> epsilon) -> epsilon)$
]

#symb[
  $S$, унифицирующее систему уравнений на типы $E = { Alpha_1 ~ Beta_1, dots, Alpha_n ~ Beta_n }$ введем обозначение $S tack.double E$.
]

#theorem[
  Для любых терма $M in Lambda$, контекста $Gamma$ ($"FV"(M) subset.eq "dom"(Gamma)$) и типа $Alpha in TT$ существует конечное множество уравнений на типы $E = E(Gamma, M, Alpha)$, такое что для любой подстановки $S$
  - $S tack.double E(Gamma, M, Alpha) => S(Gamma) tack M : S(Alpha)$
  - $S(Gamma) tack M : S(Alpha) => S' tack.double E(Gamma, M, Alpha)$ для некоторой $S'$, имеющего тот же эффект, что и $S$, на типовых переменных в $Alpha$ и $Gamma$
]

Алгоритм построения системы ограничений $E$:
$ & E(Gamma, x, Alpha) && = { Alpha ~ Gamma(x) } \
  & E(Gamma, P med Q, Alpha) && = E(Gamma, P, alpha -> Alpha) union E(Gamma, Q, alpha) \
  & E(Gamma, lambda x.med P, Alpha) && = E((Gamma, x^alpha), P, beta) union { alpha -> beta ~ Alpha }
$
где переменные $alpha, beta$ --- свежие
== Главная пара и главный тип. Теорема Хиндли-Милнера.
#definition[
  Для $M in Lambda$ *главной парой* называют пару $(Gamma, Alpha$) такую что
  - $Gamma tack M : Alpha$
  - $Gamma' tack M : Alpha' => exists S med S(Gamma) subset.eq Gamma' and S(Alpha) equiv Alpha'$
]

#theorem([Хиндли-Милнера])[
  Существует алгоритм $"PP"$, возвращающий для $M in Lambda$
  - главную пару $(Gamma, Alpha)$, если $M$ имеет тип
  - сообщение об ошибке в противном случае
]

Пусть $"FV"(M) = {x_1, dots, x_n}$. Выберем произвольные различные переменные $alpha_0, dots, alpha_n$ и сконструируем $Gamma_0 = { x_1^(alpha_1), dots, x_n^(alpha_n) }$

Алгоритм $"PP"$
$ & "PP"(M) | U(E(Gamma_0, M, alpha_0)) equiv #[ошибка] && = #[ошибка] \
  & "PP"(M) | U(E(Gamma_0, M, alpha_0)) equiv S && = (S(Gamma_0), S(alpha_0))
$

#definition[
  Для $M in Lambda^0$ *главным типом* называют тип $Alpha$, такой что
  - $tack M : Alpha$
  - $tack M : Alpha' => exists S med S(A) equiv A'$
]

#corollary[
  Существует алгоритм PT, возвращающий для $M in Lambda^0$
  - главный тип $Alpha$, если $M$ имеет тип
  - сообщение об ошибке в противном случае
]
#remark[ $Lambda^0$ --- комбинаторы #fixme() ]
== Обобщения алгоритма Хиндли-Милнера. let-полиморфизм и его ограничения
Можно расширить ХМ из:
- листья образованы только переменными
- узлы образованы только #raw("(->) :: * -> * -> *", lang: "hs")
в:
- листья --- конструкторы типа кайнда `*`
- узлы --- конструкторы типа любых стрелочных кайндов
- узлы --- полиморфные, например, `m a` или `t m a`

ХМ не справляется на #raw("\f -> (f 'z', f True)", lang: "hs"). Конструкция `let ... in ...` не просто сахар для лямбды, это отдельный примитив. Можем писать #raw("let f = \x -> x in (f 'z', f True)", lang: "hs"). В таком случае #raw("f :: forall a. a -> a", lang: "hs").

Однако не все можно написать: #raw("let f g = (g 'c', g True) in f id", lang: "hs"). `let` может только в поверхностные кванторы, а в примере выше хотим тип $(forall alpha. alpha -> alpha) -> angle.l #[`Char`], #[`Bool`] angle.r$. Нужно включить `RankNTypes` и явно указать тип `f`.
= Haskell
#let hs(text) = raw(text, lang: "hs")

== Основы программирования на Haskell. Связывания. Рекурсия. Базовые конструкции языка. Частичное применение. Бесточечный стиль.
Очев. + guards

#remark[ Развер туплов от $2$ до $15$ (по стандарту), 63 в GHC ]
== Основные встроенные типы языка Haskell. Параметрический полиморфизм. Система модулей.
`Bool`, `Char`, `Int`, `Integer`, `Float`, `Double`, `->`, `[]`
== Операторы и их сечения в Haskell.
$ #hs("(2 *+*)") equiv #hs("(*+*) 2") equiv #hs("\y -> 2 *+* y") $
$ #hs("(*+* 3)") equiv #hs("\x -> x *+* 3") $
== Строгие и нестрогие функции. Ленивое и энергичное исполнение. Форсирование, слабая головная нормальная форма.
#remark[
  ```hs
  ignore x = r2
  ```
  #hs("ignore undefined") не упадет, потому что `ignore` *не строгая* по аргументу `x`.
  ```hs
  seq :: a -> b -> b
  seq ⊥ b = ⊥
  seq a b = b
  ```
  Это не настоящий код. Но фактически `seq` вычисляет первый агрумент чтобы проверить что это не $bot$. Вычисляет оно до WHNF --- лямбды или конструктора
  ```hs
  infixr 0 $!
  ($!) :: (a -> b) -> a -> b
  f $! x = x `seq` f x
  ```
]

#remark[
  Неэффективный факториал
  ```hs
  factorial n = helper 1 n where
    helper acc k | k > 1 = helper (acc * k) (k - 1)
                 | otherwise = acc
  ```
  В `acc` будет собираться thunk #hs("(... ((1 * n) * (n - 1)) * (n - 2) * ... * 2)") потому что `helper` не строгий по `acc`. Можем форсировать вычисление:
  ```hs
  factorial n = helper 1 n where
    helper acc k | k > 1 = (helper $! (acc * k)) (k - 1)
                 | otherwise = acc
  ```
]

== Списки, стандартные функции для работы с ними. Генерация (выделение) списков.
#remark[
  Выделение списка (List Comprehension)
  ```hs
  [ [x, y] | x <- "ABC", y <- "de" ] = ["Ad", "Ae", "Bd", ...]
  ```
]
== Алгебраические типы данных. Сопоставление с образцом, его семантика. Полиморфные и рекурсивные типы данных.
#remark[ Паттерн матчинг делает функция строгой по этому аргументу ]
== Трансляция образцов в Kernel. Синонимы в образцах, ленивые и охранные образцы. Образцы в $lambda$- и let-выражениях.
#remark[
  Ленивые паттерны
  ```hs
  (***) :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
  (***) f g ~(x, y) = (f x, g y)
  ```
  Всегда успешно, связывание откладывается до момента использования

  Использование паттернов в `let` также транслируется в ленивые паттерны
  $ #hs("let p = e1 in e") equiv #hs("case e1 of ~p -> e") $
]

#remark[
  Более мощные гарды
  ```hs
  firstOdd :: [Integer] -> Integer
  firstOdd xs | Just x <- find odd xs = x
              | otherwise = 0

  firstOddIsBig :: [Integer] -> Bool
  firstOddIsBig xs
    | Just x <- find odd xs, x > 1000 = True
    | otherwise
  ```
]
== Объявления type и newtype. Метки полей. Строгие конструкторы данных.
#remark[
  Можно конструировать указывая не все поля, ошибка вылетит если попытаться использовать неинициализированные.
]

#remark[
  Так можно
  ```hs
  data Homo = Known {name :: String, male :: Bool}
            | Unknown {male :: Bool}
  ```
]

#remark[
  Можно форсировать вычисление "полей"
  ```hs
  infix 6 :+
  data Complex a = !a :+ !a
  ```

  Но
  ```
  GHCi> case 1 :+ undefined of _ -> 42
  42
  ```
  Т.к. конструктор не был вычислен
]
== Классы типов. Объявления представителей. Классы типов `Eq`, `Ord`, `Enum` и `Bound`.
```hs
class Eq a where
  (==), (/=) :: a -> a -> Bool
  x /= y = not (x == y)
  x == y = not (x /= y)
  {-# MINIMAL (==) | (/=) #-}
```

```hs
class Eq a => Ord a where
  (<), (<=), (>=), (>) :: a -> a -> Bool
  max, min :: a -> a -> a
```
Законы `Ord`:
```hs
∀ x. x <= x -- Reflexivity
∀ x y z. x <= y && y <= z ≡ x <= z -- Transitivity
∀ x y. x <= y && y <= x ≡ x == y -- Antisymmetry
∀ x. x <= y || y <= x -- Comparability
```

#remark[ Про `OrphanInstances` ]
#remark[ Про `GeneralizedNewtypeDeriving` ]
#remark[
  Про `DerivingStrategies`
  ```hs
  {-# LANGUAGE DerivingStrategies #-}
  newtype Temperature = Temperature {getTemp :: Double}
    deriving (Num,Eq)
    deriving newtype Show
  ```
]

#remark[ Про фантомные типовые параметры ]

Минимальное полное определение `toEnum`, `fromEnum`
```hs
class Enum a where
  succ, pred :: a -> a
  toEnum :: Int -> a
  fromEnum :: a -> Int
  enumFrom :: a -> [a] -- [n..]
  enumFromThen :: a -> a -> [a] -- [n,n'..]
  enumFromTo :: a -> a -> [a] -- [n..m]
  enumFromThenTo :: a -> a -> a -> [a] -- [n,n'..m]
```

```hs
class Bounded a where
  minBound, maxBound :: a
```
== Стандартные классы типов: `Num` и его наследники.
MCD: все, кроме `negate` или `(-)`
```hs
class (Eq a, Show a) => Num a where
  (+), (-), (*) :: a -> a -> a
  negate :: a -> a
  abs, signum :: a -> a
  fromInteger :: Integer -> a

  x - y = x + negate y
  negate x = 0 - x
```
Подклассы:
- `Integral` --- целочисленное деление (через `Real`) (`Integer`, `Int`)
- `Fractional` --- обыное деление (`Float`, `Double`)

#remark[
  Преобразования
  - #hs("fromIntegral :: (Num b, Integral a) => a -> b")
  - #hs("ceiling, floor, truncate, round :: (RealFrac a, Integral b) => a -> b")
]

#remark[
  Рациональные дроби
  ```hs
  data Ratio a = !a :% !a deriving (Eq)
  (%) :: Integral a => a -> a -> Ratio a
  numerator, denominator :: Integral a => Ratio a -> a

  type Rational = Ratio Integer
  ```

  Преобразование в рациональные числа:
  - `toRational float`
  - `approxRational 4.9 0.1 = 49 % 10`
]
== Стандартные классы типов: `Show` и `Read`.
```hs
type ShowS = String -> String
class Show a where
  show :: a -> String

  shows :: a -> ShowS
```
#remark[
  С помощью `shows` можем гарантированно складывать строки начиная с конца, это будет линейно. Не собираем промежуточные строки
]

```hs
type ReadS a = String -> [(a, String])

class Read a where
  read :: String -> a

  reads :: ReadS a
```
== Полугруппы и моноиды. Представители класса типов `Monoid`.
MCD: `(<>)`, `sconcat`
```hs
infixr 6 <>
class Semigroup a where
  (<>) :: a -> a -> a

  sconcat :: NonEmpty a -> a

  stimes :: Integral b => b -> a -> a
  stimes = stimesDefault
```
Законы
$ #hs("(x <> y) <> z") equiv #hs("x <> (y <> z)") $
#example[ Список ]

```hs
class Semigroup a => Monoid a where
  {-# MINIMAL mempty | mconcat #-}
  mempty :: a
  mempty = mconcat []

  -- In a future GHC release will be removed
  mappend :: a -> a -> a
  mappend = (<>)

  mconcat :: [a] -> a
  mconcat = foldr mappend mempty
```
Законы
$ #hs("mempty <> x") equiv #hs("x") \
  #hs("x <> mempty") equiv #hs("x") \
  #hs("mconcat") equiv #hs("foldr (<>) mempty") \
$

#example[ Список, для `Bool` `All`, `Any`, для чисел `Sum`, `Product`, `Min` ]
== Правая и левая свёртки списков. Энергичные версии. Развертки.
```hs
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = x `f` (foldr f z xs)
```

#remark[ У левой свертки `foldl` таскается большой thunk, поэтому есть строгая версия `foldl'` ]

#remark[ `foldr1`, `foldl1`, `scanl` ]

#remark[
  ```hs
  unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
  unfoldr g ini
    | Nothing <- next = []
    | Just (a,b) <- next = a : unfoldr g b
    where next = g ini
  ```
]
== Класс типов `Foldable` и его представители.
```hs
class Foldable t where
  foldr, foldr' :: (a -> b -> b) -> b -> t a -> b
  foldr f z t = appEndo (foldMap (Endo . f) t) z

  foldl, foldl' :: (a -> b -> a) -> a -> t b -> a
  foldl f z t = appEndo
    (getDual (foldMap (Dual . Endo . flip f) t)) z

  foldr1, foldl1 :: (a -> a -> a) -> t a -> a

  fold :: Monoid m => t m -> m
  fold = foldMap id

  foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap f = foldr (mappend . f) mempty

  {-# MINIMAL foldMap | foldr #-}

  toList :: t a -> [a]

  null :: t a -> Bool
  null = foldr (\_ _ -> False) True

  length :: t a -> Int
  length = foldl' (\n _ -> n + 1) 0

  elem :: Eq a => a -> t a -> Bool

  sum, product :: Num a => t a -> a
  sum = getSum . foldMap Sum
  maximum, minimum :: Ord a => t a -> a
```

#example[ Список, `Maybe`, `Either`, туплы ]

Функции обобщенные до использования `Foldable`
```hs
concat :: Foldable t => t [a] -> [a]
concatMap :: Foldable t => (a -> [b]) -> t a -> [b]

and,or :: Foldable t => t Bool -> Bool
any,all :: Foldable t => (a -> Bool) -> t a -> Bool

maximumBy,minimumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a

notElem :: (Foldable t, Eq a) => a -> t a -> Bool

find :: Foldable t => (a -> Bool) -> t a -> Maybe a
```
== Класс типов `Functor` и его представители.
```hs
infixl 4 <$, <$>, $>
class Functor f where
  fmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a
  (<$) = fmap . const

(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap
($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)
```

#example[ Список, `Maybe`, какой-нибудь `Tree`, `Either`, тупл, `(->) e` ]

Другие полезные функции
```hs
void :: Functor f => f a -> f ()
void xs = () <$ xs

infixl 1 <&>
(<&>) :: Functor f => f a -> (a -> b) -> f b
xs <&> g = g <$> xs

unzip :: Functor f => f (a, b) -> (f a, f b)
unzip xs = (fst <$> xs, snd <$> xs
```

Законы
$ #hs("fmap id") equiv #hs("id") \
  #hs("fmap (f . g)") equiv #hs("fmap f . fmap g") 
$

#remark[
  Для чего нельзя правильный написать функтор:
  ```hs
  newtype Endo a = Endo { appEndo :: a -> a }
  ```
  А для перевернутой стрелки вообще нельзя написать функтор
]
== Класс типов `Applicative` и его представители.
```hs
infixl 4 <*>, *>, <*, <**>
class Functor f => Applicative f where
  {-# MINIMAL pure, ((<*>) | liftA2) #-}
  pure :: a -> f a

  (<*>) :: f (a -> b) -> f a -> f b
  (<*>) = liftA2 id

  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  liftA2 g a b = g <$> a <*> b

  (*>) :: f a -> f b -> f b
  u *> v = (id <$ u) <*> v

  (<*) :: f a -> f b -> f a
  u <* v = liftA2 const u v
```

#example[ `Maybe`, список: каждый с каждым, попарно `ZipList`, пара с `Monoid` ]

Законы 
$ #hs("fmap g . pure") equiv #hs("pure . g") \
  #hs("fmap g xs") equiv #hs("pure g <*> xs") \
  #hs("pure id <*> v") equiv #hs("v") \
  #hs("pure g <*> pure x") equiv #hs("pure (g x)") \
  #hs("u <*> pure x") equiv #hs("pure ($ x) <*> u") \
  #hs("pure (.) <*> u <*> v <*> x") equiv #hs("u <*> (v <*> x)")
$
== Классы типов `Alternative` и `MonadPlus` и их представители.
```hs
class Applicative f => Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
infixl 3 <|>
```

#remark[
  Население
  - `Maybe` --- первый не `Nothing` (как обретка `First`)
  - `ZipList` --- если первый кончился, он дополняется элементами из второго
]

Для `IO`
```hs
instance Alternative IO where
  empty :: IO a
  empty = failIO "mzero"

  (<|>) :: IO a -> IO a -> IO a
  m <|> n = m `catchException` \(_ :: IOError) -> n
```

```hs
class (Alternative m, Monad m) => MonadPlus m where
  mzero :: m a
  mzero = empty

  mplus :: m a -> m a -> m a
  mplus = (<|>)
```

Законы
$ #hs("mzero >>= k") equiv #hs("mzero") \
  #hs("v >> mzero") equiv #hs("mzero")
$
И как минимум одного из двух:
$ #hs("(a `mplus` b) >>= k") equiv #hs("(a >>= k) `mplus` (b >>= k)") \
  #hs("return a `mplus` b") equiv #hs("return a")
$

#remark[
  `guard`
  ```hs
  asum :: (Foldable t, Alternative f) => t (f a) -> f a
  asum = foldr (<|>) empty

  msum :: (Foldable t, MonadPlus m) => t (m a) -> m a
  msum = asum -- foldr mplus mzero
  ```
  ```hs
  mfilter :: MonadPlus m => (a -> Bool) -> m a -> m a
  mfilter p ma = do
    a <- ma
    if p a
    then return a
    else mzero
  ```
]
== Аппликативные парсеры.
```hs
newtype Parser tok a =
  Parser { runParser :: [tok] -> Maybe ([tok],a) }

satisfy :: (tok -> Bool) -> Parser tok tok
satisfy pr = Parser f where
  f (c:cs) | pr c = Just (cs,c)
  f _ = Nothing

lower :: Parser Char Char
lower = satisfy isLower

char :: Char -> Parser Char Char
char c = satisfy (== c)

instance Functor (Parser tok) where
  fmap :: (a -> b) -> Parser tok a -> Parser tok b
  fmap g = Parser . (fmap . fmap . fmap) g . runParser

digit :: Parser Char Int
digit = digitToInt <$> satisfy isDigit

instance Applicative (Parser tok) where
  pure :: a -> Parser tok a
  pure x = Parser $ \s -> Just (s, x)
  (<*>) :: Parser tok (a -> b) -> Parser tok a -> Parser tok b
  Parser u <*> Parser v = Parser f
    where
      f xs = case u xs of
        Nothing -> Nothing
        Just (xs', g) -> case v xs' of
          Nothing -> Nothing
          Just (xs'', x) -> Just (xs'', g x)

instance Alternative (Parser tok) where
  empty :: Parser tok a
  empty = Parser $ \_ -> Nothing

  (<|>) :: Parser tok a -> Parser tok a -> Parser tok a
  Parser u <|> Parser v = Parser f
    where
      f xs = case u xs of
        Nothing -> v xs
        z -> z
```
== Класс типов `Traversable` и его представители.
MCP: `sequenceA` или `traverse`
```hs
class (Functor t, Foldable t) => Traversable t where
  sequenceA :: Applicative f => t (f a) -> f (t a)
  sequenceA = traverse id

  traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  traverse g = sequenceA . fmap g
```

Законы
$ #hs("traverse Identity") equiv #hs("Identity") \
  #hs("traverse (Compose . fmap f . g)") equiv #hs("Compose . fmap (traverse f) . traverse g") \
  #hs("h . traverse f") equiv #hs("traverse (h . f)")
$
Эти законы гарантируют
- Траверсы не пропускают элементов
- Траверсы посещают элементы не более одного раза
- `traverse pure` дает `pure`
- Траверсы не изменяют исходную структуру --- она либо сохраняется, либо полностью исчезает
== Монады. Класс типов `Monad`. Законы монад. `do`-нотация.
```hs
infixl 1 >>, >>=
class Applicative m => Monad m where
  {-# MINIMAL (>>=) #-}
  (>>=) :: m a -> (a -> m b) -> m b -- произносят bind

  (>>) :: m a -> m b -> m b
  m1 >> m2 = m1 >>= \_ -> m2

  return :: a -> m a
  return = pure
```

#remark[ Экземпляры: `Maybe` ]

Законы
$ #hs("return a >>= k") equiv #hs("k a") \
  #hs("m >>= return") equiv #hs("m") \
  #hs("(m >>= k) >>= k'") equiv #hs("m >>= (\x -> k x >>= k')")
$

Законы в терминах `join`
$ #hs("join . return") equiv #hs("id") \
  #hs("join . fmap return") equiv #hs("id") \
  #hs("join . fmap join") equiv #hs("join . join")
$
== Класс типов `MonadFail`, его история и представители.
```hs
class Monad m => MonadFail m where
  fail :: String -> m a

instance MonadFail Maybe where
  fail _ = Nothing
```

Закон: `fail s` это левый ноль для `>>=`
$ #hs("fail s >>= k") equiv #hs("fail s") $
== Стандартные монады: `Maybe` и списки.
#remark[ Списки flat'ятся ]
== Ввод-вывод в чистых языках. Монада `IO`. Взаимодействие с файловой системой.
```hs
newtype IO a =
  IO (State# RealWorld -> (# State# RealWorld, a #))
```

```hs
getChar :: IO Char
getLine :: IO String
getContents :: IO String

putChar :: Char -> IO ()
putStr, putStrLn :: String -> IO ()
print :: Show a => a -> IO ()

interact :: (String -> String) -> IO ()
```
== Монада `Reader`.
```hs
instance Monad (Reader r) where
  return x = reader $ \_ -> x
  m >>= k = reader $ \e -> let v = runReader m e
                             in runReader (k v) e
```

```hs
reader :: (r -> a) -> Reader r a
runReader :: Reader r a -> r -> a
```

#remark[ `ask`, `asks`, `local` ]
== Монада `Writer`.
```hs
instance Monoid w => Monad (Writer w) where
  return x = writer (x, mempty)

  m >>= k = let (x,u) = runWriter m
                (y,v) = runWriter $ k x
              in writer (y, u `mappend` v)
```

```hs
writer :: (a, w) -> Writer w a
runWriter :: Writer w a -> (a, w)
```

#remark[ `tell`, `listen :: Writer w a -> Writer w (a, w)`, `listens`, `censor :: (w -> w) -> Writer w a -> Writer w a` ]
== Монада `State`.
```hs
newtype State s a = State { runState :: s -> (a,s) }

state :: (s -> (a,s)) -> State s a
runState :: State s a -> s -> (a,s)
```

```hs
instance Monad (State s) where
  return x = state $ \st -> (x,st)
  m >>= k = state $
    \st -> let (x,st') = runState m st
               m' = k x
             in runState m' st'
```

```hs
get :: State s s
get = state $ \s -> (s,s)

put :: s -> State s ()
put s = state $ \_ -> ((),s)

modify :: (s -> s) -> State s ()
modify f = do s <- get
              put (f s)

gets :: (s -> a) -> State s a
gets f = do s <- get
            return (f s)
```

#remark[ `replicateM` ]

#remark[
  - Монада `ST`, `runST :: (forall s. ST s a) -> a`. Можно делать "нечистые" вычисления в чистых функциях
  - `IORef` это `STRef` без локальности и соответствующих гарантий безопасности
  - `MVar` это `IORef` с блокировками
  - `TVar` это изменяемые ячейка памяти в рамках STM
]
== Монада `Except`.
```hs
newtype Except e a = Except { runExcept :: Either e a }

except :: Either e a -> Except e a
except = Except

instance Monad (Except e) where
  return :: a -> Except e a
  return a = except $ Right a

  (>>=) :: Except e a -> (a -> Except e b) -> Except e b
  m >>= k = case runExcept m of
    Left e -> except $ Left e
    Right x -> k x

throwE :: e -> Except e a
throwE = except . Left

catchE :: Except e a -> (e -> Except e' a) -> Except e' a
m `catchE` h = case runExcept m of
  Left l -> h l
  Right r -> except $ Right r
```

== Мультипараметрические классы типов. Роль классов `MonadReader`, `MonadWriter`, `MonadState` и `MonadError` в `mtl`.
```hs
class Mult a b c where
  (***) :: a -> b -> c

instance Mult Matrix Matrix Matrix where
  {- ... -}
instance Mult Matrix Vector Vector where
  {- ... -}
instance Mult Matrix Int Matrix where
  {- ... -}
instance Mult Int Matrix Matrix where
  {- ... -}
```
Но не можем сделать #hs("Matrix (Vector 1 2) (Vector 3 4) *** Matrix (Vector 1 0) (Vector 0 1)"), т.к. параметр `c` нигде явно не указан и нельзя определить инстанс `Mult`.

Можно определить "функциональную зависимость". Т.е. для каких-то `a`, `b` не может двух инстансов для двух разные `c` и `c'`
```hs
class Mult a b c | a b -> c where
  (***) :: a -> b -> c
```

Это используется в `mtl`. Можно наделить любую монаду свойствами одной из других:
```hs
class Monad m => MonadReader r m | m -> r where
  ask :: m r
  local :: (r -> r) -> m a -> m a

class (Monoid w, Monad m) => MonadWriter w m | m -> w where
  tell :: w -> m ()
  listen :: m a -> m (a, w)

class Monad m => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()

class Monad m => MonadError e m | m -> e where
  throwError :: e -> m a
  catchError :: m a -> (e -> m a) -> m a
```
== Трансформеры монад. Библиотеки `transformers` и `mtl`.
#definition[
  *Трансформер монад* --- конструктор типа, который принимает монаду в качестве аргумента и возвращает монаду как результат
]

#remark[
  ```hs
  class MonadTrans t where
    lift :: Monad m => m a -> t m a
  ```
]

#example[
  ```hs
  newtype MyMonadT m a = MyMonadT { runMyMonadT :: m (MyMonad a) }
  ```
]

#remark[ Про `fail` ]

Законы
$ #hs("lift . return") equiv #hs("return") \
  #hs("lift (m >>= k)") equiv #hs("lift m >>= (lift . k)")
$
