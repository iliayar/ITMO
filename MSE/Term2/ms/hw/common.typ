#import "/other/typst/hw_common.typ": *

#let hw(doc) = hw_with_header([
  #align(right)[
    #table(
      columns: 2,
      align: left,
      stroke: none,
      [Студент:], [Ярошевский Илья],
      [Группа], [2],
      [Дата:], [
        #icu.fmt(datetime.today(), locale: "ru", length: "long")
      ],
    )
  ]
], doc)
