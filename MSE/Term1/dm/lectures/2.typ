#import "/other/typst/lecture_mse.typ": *


#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 2],
  date: [17 сентбяря],
  number: 2,
  doc
)

= Основы перечислительной комбинаторики

#definition()[
  $A$ *поднможество* $X$, если $forall x in A ==> x in X$
]
#symb()[$A subset X$]

#definition()[
  *Мощностью* множества называется количество элементво в нем
]
#symb()[$|X|$]

#definition()[
  *Пересечением* множеств $X$ и $Y$ называется множествао $A$, такое что $forall x : x in A <=> x in X and x in Y$
]
#symb()[$X inter Y$]

#definition()[
  *Объединением* множеств $X$ и $Y$ называется множество $B$, такое что $forall x : x in A <=> x in X or x in Y$
]
#symb()[$X union Y$]

#definition()[
  *Разностью* множеств $X$ и $Y$ называется множемтво $C$, такое что $forall x : x  in C <=> x in X and x in.not Y$
]

#definition()[
  *Симметричной разностью* /* ... */ называется множество $Delta$, такое что $forall x : x in Delta <=> (x in X and x in.not Y) or (x in Y and x in.not X)$ 
]
#symb()[$X triangle Y$]

#definition()[
  *Дополнением* множества $A$ в множестве $X$ называется множество $B$, такое что $forall x in B : x in B <=> x in.not A$
]

#remark()[
  Правило суммы: $A , B : A inter B = emptyset$, $|A union B| = |A| + |B|$
]

#definition()[
  $X$ --- множество, $A_1, ..., A_n$ называется *разбиением* $X$:
  1. $A_i != emptyset quad forall i$ 
  2. $A_i inter A_j != emptyset quad forall u != j$
  3. $union.big_(i = 1)^n A_i = X$
]
#corollary_def()[
  $|X| = sum_(i = 1)^n |A_i|$
]

#remark()[
  Частные случаи, $|A| + |overline(A)| = |X|$.
  #todo()
]

#definition()[
  Декартовым произведением множест $X$ и $Y$ называется множество пар $(x, y): x in X, y in Y$
]
#symb()[$X times Y$]
#remark()[$|X times Y| = |X| dot |Y|$]

#definition()[
  Любой элемент $X^k$ называется *$k$-мультимножеством* $X$.
  #fixme()
]

#definition()[
  $ (X, phi) quad phi : X -> bb(Z)_+ $
  ,где $phi$ --- сколько раз взяли элемент. Вся пара характеризует муьтимножество
  #fixme()
]

#theorem("Формула включения исключений")[
  $A, B subset X$.
  $ |overline(A union B)| = |X| - |A union B| = |X| - |A| - |B| + |A inter B| $
]

#example()[
  Обобщается
  $ |overline(A union B union C)| = |X| - |A| - |B| - |C| + |A inter B| + |B inter C| + |C inter A| - |A inter B inter C| $
]

#theorem("Размещения с повторениями")[
  Количество способов выбрать $k$ элементов и $n$ элментного множества с учетом того что элементы могут повторяться и важен порядок выбора
  $ n^k $
]
#example()[
  Есть 20 учатсников. Сколько возмножных списков результатов из 24 раундов. #todo()
]

#theorem("Размещения без повторений")[
  Количество способов выбрать $k$ элементов и $n$ элментного множества с учетом того что элементы не могут повторяться, но важен порядок выбора
  $ n dot (n - 1) dot (n - 2) dot ... dot (n - k + 1) = frac(n!, (n - k)!) = A^k_n = n_((k)) $
]

#theorem("Перестановки без повторений")[
  Количество спобосбов упорядочить $n$-элементное множество
  $ n! = P(n) $
]
#remark()[$ P(n) = A^n_n $]

#theorem("Сочетания без повторений")[
  Количество способов выбрать $k$ элементов из $n$-элементного множества без учета порядка, с учетом того что элементы не могут повторяться
  $ C^k_n = binom(n, k) = frac(n!, k! dot (n - k)!) $
]
#example()[Количество $k$-элементных подмножеств $n$-элементного множества]
