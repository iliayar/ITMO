#import "/other/typst/lecture_mse.typ": *
#import "/MSE/Term1/dm/common.typ": *

#show: doc => lecture(
  subj: [Дискретная математика],
  title: [Лекция 8],
  date: [29 октября],
  number: 8,
  doc
)

= Колмогоровская модель теории вероятностей

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

#remark()[
  Проверим два свойства которые раньше требовали:
  3. Если $A inter B = emptyset$, то $PP(A union B) = PP(A) + PP(B)$
    #proof()[
      В свойство 3. меры подставляем $A_1 = A, A_2 = B, A_i = emptyset$.
    ]
  2. Если $A subset B$, то $PP(A) <= PP(B)$.
    #proof()[
      $B = A union (B \\ A)$, а $A union (B \\ A) = emptyset$
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
      $B = (A inter B) union (B \\ A)$, а $(A inter B) union (B \\ A) = emptyset$
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
  $ PP(inter.big_(i = 10)^infinity A_i) =^1 lim_(n -> infinity) PP(inter.big_(i = 1)^n A_i)) = lim_(n -> + infinity) product_(i = 1)^n PP(A_i) = product_(i = 1)^infinity PP(A_i) $
  // TODO(iliayar): Align center text
  1. $ lim_(n -> + infinity) PP(overbrace(inter.big_(i = 1)^n A_i, B_n)) =_#text[по непр. \ меры] PP(inter.big_(i = 1)^infinity B_i) = PP(inter.big_(i = 1)^infinity A_i) $
    По непрерывности меры: $lim_(n -> infinity) PP(B_n) = PP(inter.big_(i = 1)^infinity B_i)$
]

== Случайные величины

#definition()[
  *Случайной величиной* (с.в.) называется $xi : Omega -> R$ измеримая
]
#remark()[
  Измеримая --- если попали в какой-то элемент $sigma$-алгебры в $RR$, то должны попасть в элемент $sigma$-алгебры в $Omega$
]

#definition()[
  *Распределение случайной величины* $P_xi$ --- мера, заданная на борелевской $sigma$-алгебре $frak(B)$.
  $ P_xi (A) colon.eq PP(xi in A) = PP(omega in Omega : xi(omega) in A) $
]

#remark()[
  Случайные величины $xi$ и $eta$ совпадают если $P(xi (A) = P_eta (A)$ для любого $A$ --- борелевского. Но на самом деле достаточно совпадения на ячейках $(a; b]$.
  $ P_xi ((a; b]) = PP(A < xi <= b) = PP(xi <= b) - PP(xi <= a) $
  То есть необходимо и достаточно $forall c quad PP(xi <= c) = PP(eta <= c)$
]

#definition()[
  $F_xi (t) colon.eq PP(xi <= t)$ называется функцией распределения случайной величины $xi$.
]

// TODO(iliayar): Make theorem for properties
#remark([*Свойства*])[
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
      $ lim_(t_n -> t) PP_(B_n) = lim_(t_n -> t+) F_xi (t_n) $
      По непрерывности меры $lim_(t_n -> t) PP_(B_n) = PP(inter.big_(i = 1)^infinity B_i) = PP(xi <= t) = F_xi (t)$
    ]
  6. $PP(xi < t) = lim_(x -> t-) F_xi (x)$
    #proof()[
      $t_n$ монотонно возрастают к $t$
      $ {xi <= t_n) = B_n quad B_1 subset B_2 subset dots $
      // FIXME(iliayar): Arrow pointing from left bottom to right top instead of ->
      // And the above cases too
      $ lim_(t_n -> t) PP(B_n) = lim_(x -> t-) F_xi (x) $
      $ lim_(t_n -> t) PP(B_n) = PP(union.big_(i = 1)^infinity B_i) = PP(xi < t) $
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
  Если существует $P_xi (t) : RR -> RR$ измеримая:
  $ F_xi (t) = integral_(-infinity)^t P_xi (t) d t $
  , то $xi$ называется *абсолютно непрерывной случайной величиной*, а $P_xi (t)$ называется *плотностью распределения*
    
]

#remark([*Свойства*])[
  1. $PP(xi in A) = integral_A P_xi (t) d t$
  2. $integral_Omega P_xi (t) d t = 1$
  3. $P_xi (t) = F'_xi (t)$ почти во всех $t$
]
