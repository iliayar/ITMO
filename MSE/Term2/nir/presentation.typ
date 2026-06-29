#import "@preview/polylux:0.4.0"
#import "@preview/polylux:0.4.0": only
#import "@preview/codelst:2.0.2": sourcecode
#import "common.typ": diagrams_for
#import "@preview/zebraw:0.6.3": *
#show: zebraw.with(lang: false)

#let diagrams = diagrams_for("presentation")
#let puml = diagrams.puml

#let title-slide(title: [], author: [], notes: none) = {
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

  polylux.slide([
    #set align(center)
    #block(height: 70%)[
      #set align(horizon)
      #text(title, size: 30pt, weight: "semibold")
    ]

    #line(length: 95%)
    #author

    #{
      if notes != none [
        #metadata(notes.text) <notes>
      ]
    }
  ])
}

#let slide(title, content, notes: none) = {
  set page(
    paper: "presentation-16-9",
    header: [
      #grid(columns: (1fr, 80pt))[
        #set align(left + horizon)
        #text(title, size: 26pt, weight: "semibold")
      ][
        #set align(right + horizon)
        #image(
          "assets/itmo-logo.png",
          width: 120pt,
        )
      ]
      #v(-30pt)
      #line(length: 95%)
    ],
    footer: context [
      #set align(right)
      #set text(16pt)
      #box[
        #counter(page).display("1")
        #text("/")
        #text(str(counter(page).final().at(0)))
      ]
    ],
    margin: (
      top: 70pt,
    ),
  )

  polylux.slide([
    #set text(22pt, lang: "ru")
    #content

    #{
      if notes != none [
        // #polylux.toolbox.pdfpc.speaker-note(raw(notes.text + "\n\n**NEXT**", lang: "md"))
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
    footer: context [
      #set align(right)
      #set text(16pt)
      #box[
        #counter(page).display("1")
        #text("/")
        #text(str(counter(page).final().at(0)))
      ]
    ],
    margin: (
      top: 90pt,
    ),
  )

  polylux.slide([
    #set text(40pt, lang: "ru")
    #set align(center + horizon)
    Спасибо за внимание

    #{
      if notes != none [
        // #polylux.toolbox.pdfpc.speaker-note(notes)
        #metadata(notes.text) <notes>
      ]
    }
  ])
}

#show raw.where(lang: "cangjie"): set raw(
    syntaxes: ("Cangjie.sublime-syntax",),
)

#set text(font: "Arial")

#title-slide(
  title: [Визуализация промежуточного AST языка Cangjie], 
  author: [
    #set text(16pt)
    Студент: Ярошевский Илья Андреевич \
    Руководитель: Беляев Михаил Анатольевич
  ]
)

#slide([Преобразования AST в процессе компиляции])[
  - Синтаксический сахар
  - Инструментация на этапах после семантического анализа
    
    Например, замена обращений к полям на вызов getter метода, для mock тестирования:
    #raw(lang: "cangjie", "obj.x") $|->$ #raw(lang: "cangjie", "obj.x$get()")

  - Инстанциация обобщенных определений
]

#slide([Отладка рассахаренного AST])[
  #grid(columns: 3, gutter: 4pt, [
    Существует опция для генерации текстового представления AST, однако оно достаточно многословно

    ```cangjie
    func sum(x: Int, y: Int) {
      return x + y
    }
    ```
  ], [
    #image("assets/1.png")
  ], [
    #image("assets/2.png")
  ])
]

#slide([Отладка рассахаренного AST])[
  - Сложно разглядеть структуру дерева сквозь огромное количество мета-информации
  - Текстовый поиск по адресу для определения целевой декларации ссылки
    ```
    FuncParam: y {
      ptr: 0x7bcdb8007420
    }
    RefExpr: y {
      target ptr: 0x7bcdb8007420
    }
    ```
]

#slide([Существующие решение и требования])[
  Существующие инструменты тесно связаны с языком, для которого они сделаны:

  _TypeScript_ AST Viewer, ACAV(_C/C++_), _Kotlin_ FIR Viewer, ...

  Инструмент должен предоставлять:
  - Интерактивные ссылки на определения
  - Мета-информация для конкретного узла
  - Приближенный исходный код рассахаренного AST
]

#slide([Цель и задачи])[
  *Цель*: Упростить отладку предоставив интерактивный инструмент для отображения AST

  *Задачи*:
  - Реализация отображения AST в представление, близкое к синтаксически корректному коду
  - Реализация отображения AST в машиночитаемый формат
  - Реализация графического интерфейса для отображения AST
]

#slide([Форматирование рассахаренного AST])[
  #grid(
    columns: 2,
    [
      На основе существующего форматера `cjfmt`:
      - Реализовано сохранение позиций узлов относительно отформатированного кода
      - Дополнительная обработка некоторых случаев
    ],
    [
      #image("assets/3.png")
    ]
  )
]

#slide([Отображение AST в JSON])[
  - Построение отображения узел $<->$ идентификатор
  - Сохранение ссылок на определения
  - Сбор мета-информации
  ```json
{
    "stages": {
        "genericinst":{
            "nodes":[ {"id":1,"children":[2], ...}, ... ],
            "sources":{"other.cj":"..."}
        }
    }
}
  ```
]

#slide([Графический интерфейс])[
  #align(center)[#image("assets/4.png", height: 61%)]
  - Отформатированное AST, представление в виде дерева, мета-информация выделенного узла
  - Краткая мета-информация при наведение, поддержка нескольких файлов, выбор стадии преобразования AST
]

#slide([Архитектура])[
  // left to right direction
  #puml(name: "001-arch")[```
  @startuml

  skinparam linetype ortho
  skinparam defaultFontName Arial
  skinparam defaultFontSize 22
  skinparam defaultTextAlignment center
  skinparam componentStyle rectangle

  component [libcangjie-lsp.so] #green

  component [Исходный код] #line.dashed

  component [Итоговый HTML] #line.dashed

  component "cjexplore" {
    component [CompilerInstance] #green
    [CompilerInstance] .u.> [libcangjie-lsp.so]

    [Исходный код] --> [CompilerInstance]

    component [JSON представление] #line.dashed
    component [AST] #line.dashed
    component [Генератор JSON представления] #yellow
    component [Рассахаренный исходный код] #line.dashed

    [CompilerInstance] --> [AST]
    [AST] -r-> [cjfmt с сохранением позиций]
    [AST] --> [Генератор JSON представления]

    [cjfmt с сохранением позиций] --> [Рассахаренный исходный код] 
    [Рассахаренный исходный код] --> [Генератор JSON представления]

    component [HTML шаблон] #yellow

    [Генератор JSON представления] -r-> [JSON представление]

    [JSON представление] -r-> [Итоговый HTML]
    [HTML шаблон] --> [Итоговый HTML]

    component [cjfmt с сохранением позиций] #yellow
  }

  @enduml
  ```]
]

#slide([Утилита cjexplore])[
  #align(center)[
    #zebraw(lang: false, numbering: false, ```sh
    $ cjc       lib.cj --output-type=staticlib --mock=on
    $ cjexplore lib.cj --output-type=staticlib --mock=on \
      --ast-stages=sema,genericinst
    [cjexplore] Compiling to stage: sema...
    [cjexplore] Compiling to stage: genericinst...
    [cjexplore] Written to other.cj.html
    ```)
  ]
  - Используется предоставляемая в SDK библиотека с компилятором: `libcangjie-lsp.{so,dylib}`
  - Интерфейс совместим с интерфейсом компилятора `cjc`
]

#slide([Результаты и выводы])[
  - Реализован прототип инструмента для интерактивного отображения рассахаренного AST
  - Инструмент протестирован в реальных задачах и по отзывам оказался гораздо удобнее прежних способов отладки

  Дальнейшая работа:
  - Больше мета-информации
  - Поддержка нескольких пакетов
  - Аналогичный функционал для промежуточного представления CHIR
]
