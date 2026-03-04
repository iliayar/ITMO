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

#let hw_with_header(header, doc) = {
  set page(
    footer: context [
      #align(center)[
        #counter(page).display()
      ]
    ],
  )

  header

  setup_common(doc)
}

