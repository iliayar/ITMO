#import "@preview/codelst:2.0.1": sourcecode
#import "common.typ": diagrams_for
#import "@preview/drafting:0.2.0": *
#import "@preview/algorithmic:0.1.0"

#import algorithmic: algorithm

#let diagrams = diagrams_for("thesis")
#let puml = diagrams.puml
#let start_page = 4

#let default-text-size = 14pt
#let default-indent = 1.25cm
#set text(
  size: default-text-size, 
  font: "Times New Roman",
  lang: "ru",
)

#set page(
  margin: (
    left: 30mm,
    right: 15mm,
    top: 20mm,
    bottom: 20mm
  ),
  header: context [
    #let page-number = counter(page).get().first()
    #align(center)[#numbering("1", page-number + start_page - 1)]
  ]
)

#set par(
  leading: 1.25em,
  justify: true,
  hanging-indent: -default-indent,
)

#show heading: it => {
  align(center)[
    #text(size: default-text-size, weight: "semibold")[#it]
  ]
}

#set heading(numbering: (num, ..nums) => 
  if nums.pos().len() == 0 { none } 
  else if nums.pos().len() == 1 { 
    numbering("ГЛАВА 1.", nums.pos().first())
  } else {
    numbering("1.", ..nums)
  }
)

#show figure.where(kind: "listing"): set block(breakable: true)

#let listing = (caption, it) => {
 figure(
  par(hanging-indent: 0cm, justify: false)[
   #sourcecode(frame: none)[#it]
  ],
  caption: caption,
  kind: "listing",
  supplement: [Листинг],
 )
}

#let algo = (caption: none, it) => {
  figure(
    par(hanging-indent: 0cm, leading: 1em, justify: false, align(left, algorithm(it))),
    caption: caption,
    kind: "listing",
    supplement: [Листинг],
  )
}

#let conclusion = it => [
  #set heading(numbering: none)
  === #it
]

#let wref = (supplement, label-id) => {
  if sys.inputs.gen-diagrams != "yes" {
    ref(label(label-id), supplement: supplement)
  } else []
}

#show outline.entry: it => {
  let indent-level = calc.max(0, it.level - 2)
  let indent = indent-level * default-indent
  [
    #box(width: 100% - 1em * (indent-level + 1), outset: 0pt)[
      #par(
        hanging-indent: indent + default-indent
      )[
        #h(indent)#text(size: default-text-size)[#it.body]#box(width: 1fr, it.fill)
      ]
    ]#box(width: 1fr, it.fill, outset: 0pt)#it.page
  ]
}

#set-page-properties()

= СОДЕРЖАНИЕ

#par(hanging-indent: 0cm)[
  #outline(
    title: none, 
    indent: none,
  )
]

#pagebreak()
= ВВЕДЕНИЕ

Введение

#pagebreak()

== Обзор
=== Термины и понятия
- *Пример*~-- пример.

=== Примеры

Пример на #wref([рисунке], "example-diagram") и в #wref([листинге], "example-listing") из ресурса @example.

#puml(name: "001-example", caption: [Пример диаграмы])[```
@startuml

skinparam actorStyle awesome
skinparam linetype polyline
skinparam linetype ortho
skinparam defaultFontName Times New Roman
skinparam defaultTextAlignment center

left to right direction

actor user as "Пользователь"
node endpoint as "Endpoint"

user -r-> endpoint

@enduml
```] <example-diagram>

#listing([Пример листинга])[```ocaml
let main = print_endline "Hello"
```] <example-listing>
#conclusion[Выводы по Главе 1]

Выводы

#pagebreak()

= ЗАКЛЮЧЕНИЕ

Заключение

#pagebreak()

#bibliography(
  "bib.yml", 
  title: [БИБЛИОГРАФИЧЕСКИЙ СПИСОК],
  style: "gost-r-705-2008-numeric"
)
