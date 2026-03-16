#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 5],
  date: [11 марта],
  number: 5,
  author: "Ярошевский Илья",
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  $ prooftree(
      rule(
        rule(A prec.eq A inter A, name: "(A4)"),
        rule(
          A prec.eq B_1,
          A prec.eq B_2,
          A inter A prec.eq B_1 inter B_2,
          name: "(R1)",
        ), 
        A prec.eq B_1 inter B_2,
        name: "(R3)"
      )
    ) $
]

#task(numbering: (..) => numbering("1", 2))[
  $ prooftree(
      rule(
        (1),
        rule((A_1 inter A_2 -> B_1) inter (A_1 inter A_2 -> B_2) prec.eq A_1 inter A_2 -> B_1 inter B_2, name: "(A7)"),
        (A_1 -> B_1) inter (A_2 -> B_2) prec.eq A_1 inter A_2 -> B_1 inter B_2,
        name: "(R3)"
      )
    ) $

  $ prooftree(
      rule(
        rule(
          rule(A_1 inter A_2 prec.eq A_1, name: "(A5)"),
          rule(B_1 prec.eq B_1, name: "(A1)"),
          A_1 -> B_1 prec.eq A_1 inter A_2 -> B_1,
          name: "(R2)",
        ),
        rule(
          rule(A_1 inter A_2 prec.eq A_2, name: "(A6)"),
          rule(B_2 prec.eq B_2, name: "(A1)"),
          A_2 -> B_2 prec.eq A_1 inter A_2 -> B_2,
          name: "(R2)",
        ),
        (A_1 -> B_1) inter (A_2 -> B_2) prec.eq (A_1 inter A_2 -> B_1) inter (A_1 inter A_2 -> B_2),
        label: (1),
        name: "(R1)",
      )
    ) $
]

#task(numbering: (..) => numbering("1", 3))[
  $ prooftree(
      rule((A -> B_1) inter (A -> B_2) prec.eq A -> B_1 inter B_2, name: "(A7)")
    ) $
  $ prooftree(
      rule(
        rule(A -> B_1 inter B_2 prec.eq (A -> B_1 inter B_2) inter (A -> B_1 inter B_2), name: "(A4)"),
        (1),
        A -> B_1 inter B_2 prec.eq (A -> B_1) inter (A -> B_2),
        name: "(R3)"
      )
    ) $
  $ prooftree(
      rule(
        rule(
          rule(A prec.eq A, name: "(A1)"),
          rule(B_1 inter B_2 prec.eq B_1, name: "(A5)"),
          A -> B_1 inter B_2 prec.eq A -> B_1,
          name: "(R2)"
        ),
        rule(
          rule(A prec.eq A, name: "(A1)"),
          rule(B_1 inter B_2 prec.eq B_2, name: "(A6)"),
          A -> B_1 inter B_2 prec.eq A -> B_2,
          name: "(R2)"
        ),
        (A -> B_1 inter B_2) inter (A -> B_1 inter B_2) prec.eq (A -> B_1) inter (A -> B_2),
        label: "(1)",
        name: "(R1)",
      )
    ) $
]

#task(numbering: (..) => numbering("1", 4))[
  Возьмем $A_1 = B_2 = A$ и $A_2 = B_1 = B$. Тогда $lambda x.med x$ можно приписать тип $A inter B -> B inter A$:
  $ prooftree(
      rule(
        rule(
          rule(
            rule("x"^(A inter B) tack x : A inter B, name: ("Ax")),
            "x"^(A inter B) tack x : B,
            name: (inter E),
          ),
          rule(
            rule("x"^(A inter B) tack x : A inter B, name: ("Ax")),
            "x"^(A inter B) tack x : A,
            name: (inter E),
          ),
          "x"^(A inter B) tack x : B inter A,
          name: (inter I),
        ),
        tack lambda x.med x : A inter B -> B inter A,
        name: (->I)
      )
    ) $

  Попробуем типизировать $lambda x.med x : (A -> B) inter (B -> A)$. На самом верху абстракция, но чтобы применить правило $(->I)$ нужно чтобы тип был стрелочный, но у нас пересечение. Помимо $(inter E)$, $(eta)$ можем применить только правило $(inter I)$, но тогда потребуется доказать $lambda x.med : A -> B$ и $lambda x.med : B -> A$, а они очевидно недоказуемы.
]
