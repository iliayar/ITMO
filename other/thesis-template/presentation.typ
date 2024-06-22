#import "@preview/polylux:0.3.1": *
#import "@preview/codelst:2.0.1": sourcecode
#import "common.typ": diagrams_for

#let diagrams = diagrams_for("presentation")
#let puml = diagrams.puml

#let title-slide(title: [], author: []) = {
  set page(
    paper: "presentation-16-9",
    header: [
      #set align(center)
      #image(
        "assets/itmo-logo.png",
        width: 120pt,
      )
      #line(length: 95%)
    ],
    margin: (
      top: 90pt,
    ),
  )

  polylux-slide([
    #set align(center)
    #block(height: 70%)[
      #set align(horizon)
      #text(title, size: 30pt, weight: "semibold")
    ]

    #line(length: 95%)
    #author
  ])
}

#let slide(title, content, notes: none) = {
  set page(
    paper: "presentation-16-9",
    header: [
      #grid(columns: (3fr, 1fr))[
        #set align(left)
        #text(title, size: 28pt, weight: "semibold")
      ][
        #set align(right)
        #image(
          "assets/itmo-logo.png",
          width: 120pt,
        )
      ]
      #line(length: 95%)
    ],
    footer: [
      #set align(right)
      #set text(16pt)
      #counter(page).display("1")
    ],
    margin: (
      top: 90pt,
    ),
  )

  polylux-slide([
    #set text(22pt, lang: "ru")
    #content

    #{
      if notes != none [
        #pdfpc.speaker-note(raw(notes.text + "\n\n**NEXT**", lang: "md"))
        #metadata(notes.text) <notes>
      ]
    }

  ])
}

#let final(notes: none) = {
  set page(
    paper: "presentation-16-9",
    header: [
      #set align(center)
      #image(
        "assets/itmo-logo.png",
        width: 120pt,
      )
      #line(length: 95%)
    ],
    margin: (
      top: 90pt,
    ),
  )

  polylux-slide([
    #set text(40pt, lang: "ru")
    #set align(center + horizon)
    Спасибо за внимание

    #{
      if notes != none [
        #pdfpc.speaker-note(notes)
        #metadata(notes.text) <notes>
      ]
    }
  ])
}

#set text(font: "Times New Roman")

#title-slide(
  title: [Тема], 
  author: [
    #set text(16pt)
    Студент: _ФИО_ \
    Научный руководитель: _ФИО_ \
    ОAО "AAA"
  ],
)

#slide([Слайд с текстом], notes: ```md
Записи к слайду с текстом
```)[
- Один
- Два
]

#slide([Слайд с диаграмой], notes: ```md
Записки к слайду с диаграмой
```)[
Разработаны новые модули библиотеки для работы с типами
#align(center)[
  #puml(name: "001-example")[```
  @startuml
  
  skinparam defaultFontName Times New Roman
  skinparam defaultTextAlignment center
  skinparam linetype ortho
  
  top to bottom direction
  
  component "Компонента 1" as Comp1
  component "Компонента 2" as Comp2

  Comp1 ..r.> Comp2
  @enduml
  ```]
]
]

#final()
