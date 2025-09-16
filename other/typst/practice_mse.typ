#import "common.typ": *
#import "practice_common.typ": *

#let inside_book = state("inside_book", false)
#let lect = counter("lect")

#let practice(
  subj: none,
  title: none,
  date: none,
  number: none,
  doc
) = {

context if not inside_book.get() {
  set heading(numbering: "1.")
  conf_common(
    organization: "ITMO MSE y2024",
    author: link("https://conspects.iliay.ar")[Конспекты],
    meta_author: "Ilya Yaroshevskiy",
    title: [#subj. #title],
    meta_title: title,
    date: date,
    doc
  )
} else [
  #if number != none { counter(heading).update(number - 1) }
  #pagebreak(weak: true)
  #v(48pt)
  #text(20pt)[#heading(level: 1, numbering: none)[#title]]
  #counter(heading).step()
  #v(24pt)
  #doc
]

}

#let lecture_book(
  title: none,
  date: none,
  doc
) = {

context inside_book.update(true)

set document(
  title: title, 
  author: "Ilya Yaroshevskiy",
)

// FIXME(iliayar): How to do it better
let find_current_heading = () => {
  let cur_page = counter(page).at(here())
  let prev_heading = none
  for heading in query(heading.where(level: 1)) {
    if counter(page).at(heading.location()) > cur_page {
      break
    }
    prev_heading = heading
  }
  prev_heading
}

set page(
  margin: (
    top: 1cm,
    bottom: 1cm,
  )
)

show link: it => [ #underline(it)#super(emoji.chain) ]

set heading(offset: 1, numbering: "1.")

// Title page
align(center + horizon, [
  #text(24pt)[#title]

  #link("https://conspects.iliay.ar")[Конспекты] \
  #date
])

pagebreak()
counter(page).update(1)

set page(
  footer: context [
    #line(length: 100%)
    #v(-10pt)
    ITMO MSE y2024
    #set align(center)
    #v(-20pt)
    #counter(page).display(
      (..nums) => 
       "Страница "  + numbering("1", nums.pos().first()) +
       " из " + numbering("1", nums.pos().last()),
      both: true
    )
  ],
)

v(48pt)
pagebreak()

set page(
  header: context {
    let heading = find_current_heading()
    // No header on first page of each lecture
    if counter(page).at(heading.location()).first() == counter(page).at(here()).first() {
      return none
    }

    [
      #let heading = find_current_heading()
      #align(left)[#heading.body]
      #v(-20pt)
      #align(right)[#title]
      #v(-10pt)
      #line(length: 100%)
    ]
  },
)

setup_common(doc)
}
