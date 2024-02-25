#import "@preview/ctheorems:1.1.0": *
#import "@preview/tablex:0.0.8": *

#let conf(
  title: none,
  date: none,
  doc
) = {
set document(
  title: title, 
  author: "Ilya Yaroshevskiy",
)

set page(
  header: locate(loc =>
  if counter(page).at(loc).first() > 1 [
    #align(right)[Лекция 3]
    #v(-10pt)
    #line(length: 100%)
  ]),
  footer: [
    #line(length: 100%)
    #v(-10pt)
    ITMO y2019
    #set align(center)
    #v(-20pt)
    #counter(page).display(
      (..nums) => 
       "Page "  + numbering("1", nums.pos().first()) +
       " of " + numbering("1", nums.pos().last()),
      both: true
    )
  ],
  margin: (
    top: 1cm,
    bottom: 1cm,
  )
)

set heading(numbering: "1.")

show outline.entry: it => {
  text(blue, it)
}
show outline.entry.where(level: 1): it => {
  v(12pt, weak: true)
  strong(it)
}

show: thmrules

align(center, [
  #text(17pt)[#title]

  Ilya Yaroshevskiy \
  #date
])

outline(indent: auto, title: [Содержание])


set math.equation(numbering: "(1)")
show ref: it => {
  let eq = math.equation
  let el = it.element
  if el != none and el.func() == eq {
    // Override equation references.
    numbering(
      el.numbering,
      ..counter(eq).at(el.location())
    )
  } else {
    // Other references as usual.
    it
  }
}

doc
}

#let lemma = thmbox("lemma", "Лемма")
#let theorem = thmbox("theorem", "Теорема")

#let corollary_of = base => thmbox("corollary", [_Следствие_]).with(base: base)
#let corollary_lemma = corollary_of("lemma")
#let corollary = corollary_of("theorem")

#let definition = thmbox("definition", "Определение")

#let example = thmplain("example", "Пример").with(numbering: none)
#let remark = thmbox("remark", [_Примечание_]).with(numbering: none)
#let task = thmbox("task", [_Задача_])
#let solution = thmplain("solution", [*Решение*]).with(numbering: none, base: "task")
