#import "/other/typst/hw_common.typ": *

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

