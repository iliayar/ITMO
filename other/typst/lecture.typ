#import "common.typ": *

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

align(center, [
  #text(17pt)[#title]

  Ilya Yaroshevskiy \
  #date
])

outline(indent: auto, title: [Содержание])


conf_common(doc)
}
