#import "common.typ": *
#import "lecture_common.typ": *

#let conf(
  title: none,
  date: none,
  doc
) = {
conf_common(
  organization: "ITMO MSE y2024",
  author: link("https://conspects.iliay.ar")[Конспекты],
  meta_author: "Ilya Yaroshevskiy",
  title: title,
  meta_title: title,
  date: date,
  doc
)
}
