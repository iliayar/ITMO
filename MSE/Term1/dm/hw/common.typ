#import "/other/typst/hw_common.typ": *

#let hl-math-answer = (body) => hl-math(body, fill: blue.transparentize(40%))

#let hw(number, doc) = hw_with_header([
  #align(right)[
    #table(
      columns: 2,
      align: left,
      stroke: none,
      [Студент:], [Ярошевский Илья],
      [Номер ДЗ:], [#number],
      [Дата:], [
        #icu.fmt(datetime.today(), locale: "ru", length: "long")
      ],
    )
  ]
], doc)

