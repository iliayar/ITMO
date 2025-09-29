#import "/other/typst/common.typ": *

#let task = task.with(
  numbering: (_, ..n) => numbering("1", ..n),
  inset: (bottom: 0pt),
)
#let solution = solution.with(
  inset: (top: 0pt),
)
#let proof = proof.with(
  inset: (top: 0pt),
)
#let lemma = lemma.with(
  base: "task",
  numbering: (_, ..n) => numbering("1.1", ..n),
  inset: (top: 0pt),
)

#let hw(doc) = {
  set page(
    footer: context [
      #align(center)[
        #counter(page).display()
      ]
    ],
  )

  align(right)[
    #table(
      columns: 2,
      align: left,
      stroke: none,
      [Студент:], [Ярошевский Илья],
      [Группа:], [1],
      [Дата:], [
        #icu.fmt(datetime.today(), locale: "ru", length: "long")
      ],
    )
  ]

  setup_common(doc)
}

