#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 3],
  date: [24 февраля],
  number: 3,
  author: "Ярошевский Илья",
  doc
)


#task(numbering: (..) => numbering("1", 1))[
  $ (lambda f^(#[`Unit`] -> A). med f med #[`unit`]) med (lambda "_"^#[`Unit`]. med M) $

  $ (lambda f^(#[`Unit`] -> A). med f med #[`unit`]) med (lambda "_"^#[`Unit`]. med M) ~> (lambda "_"^#[`Unit`]. med M) med #[`unit`] ~> M $

  $ prooftree(
      rule(
        rule(
          rule(
            Gamma"," f^(#[`Unit`] -> A) tack f : #[`Unit`] -> A,
            Gamma"," f^(#[`Unit`] -> A) tack #[`unit`] : #[`Unit`],
            Gamma"," f^(#[`Unit`] -> A) tack f med #[`unit`] : A,
            name: "(T-App)"),
          Gamma tack (lambda f^(#[`Unit`] -> A). med f med #[`unit`]) : (#[`Unit`] -> A) -> A,
          name: "(T-Abs)"),
        rule(
          rule(dots, Gamma"," "_"^#[`Unit`] tack M : A),
          Gamma tack (lambda "_"^#[`Unit`]. med M) : #[`Unit`] -> A,
          name: "(T-Abs)"),
        Gamma tack (lambda f^(#[`Unit`] -> A). med f med #[`unit`]) med (lambda "_"^#[`Unit`]. med M) : A,
        name: "(T-App)"
      )
    )
  $
]

#task(numbering: (..) => numbering("1", 2))[
  $ bold(Z) med F equiv (lambda f. med (lambda x. med f med (lambda y. med x med x med y)) med (lambda x. med f med (lambda y. med x med x med y))) med F ~> \
    ~> (lambda x. med F med (lambda y. med x med x med y)) med (lambda x. med F med (lambda y. med x med x med y)) ~> \
    ~> F med (lambda y. med (lambda x. med F med (lambda y. med x med x med y)) med (lambda x. med F med (lambda y. med x med x med y)) med y) scripts(=)_beta \
    scripts(=)_beta F med (lambda y. med (bold(Z) med F) med y)
  $
]
