#import "common.typ": *

#let conf_common(
  organization: "",
  author: none,
  meta_author: "",
  title: none,
  meta_title: none,
  meta_description: none,
  date: none,
  doc
) = {
set document(
  title: meta_title, 
  author: meta_author,
  description: meta_description,
)

set page(
  header: context(if counter(page).at(here()).first() > 1 [
    #align(right)[Лекция 3]
    #v(-10pt)
    #line(length: 100%)
  ]),
  // header: locate(loc =>
  // if counter(page).at(loc).first() > 1 [
  //   #align(right)[Лекция 3]
  //   #v(-10pt)
  //   #line(length: 100%)
  // ]),
  footer: context [
    #line(length: 100%)
    #v(-10pt)
    #organization
    #set align(center)
    #v(-20pt)
    #counter(page).display(
      (..nums) => 
       "Страница "  + numbering("1", nums.pos().first()) +
       " из " + numbering("1", nums.pos().last()),
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

show link: it => [ #underline(it)#super(emoji.chain) ]

align(center, [
  #text(17pt)[#title]

  #author \
  #date
])

outline(indent: auto, title: [Содержание])


setup_common(doc)
}
