#import "common.typ": *
#import "lecture_common.typ": *

#let conf(
  title: none,
  date: none,
  doc
) = {

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

conf_common(
  organization: "ITMO y2019",
  author: "Ilya Yaroshevskiy",
  meta_author: "Ilya Yaroshevskiy",
  title: title,
  meta_title: title,
  date: date,
  doc
)
}
