#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 10],
  date: [15 апреля],
  number: 10,
  author: "Ярошевский Илья",
  doc
)

#let lww = $lambda underline(omega)$
#let tacklww = $scripts(tack)_lww$
#let ntacklww = $scripts(tack.not)_lww$

#task(numbering: (..) => numbering("1", 1))[
  1. $ prooftree(
      rule(
        rule(
          rule(chevron.l chevron.r tack * : square, name: "(T-Axiom)"), 
          alpha^* tack alpha : *,
          name: "(T-Ini)"
        ),
        rule(
          rule(chevron.l chevron.r tack * : square, name: "(T-Axiom)"),
          alpha^* tack alpha : *,
          name: "(T-Ini)"
        ),
        alpha^*"," x^alpha tack alpha : *,
        name: "(T-WeakVar)"
      )
     ) $
  2. Можем применить только правило $"(T-WeakVar)"$:
    $ prooftree(
      rule(
        rule(
          rule(chevron.l chevron.r tack alpha : *, name: #text(red)[?]),
          x^alpha tack x : alpha,
          name: "(T-Ini)"
        ),
        rule(
          rule(chevron.l chevron.r tack alpha : *, name: #text(red)[?]),
          x^alpha tack alpha : *,
          name: "(T-WeakVar)"
        ),
        x^alpha"," alpha^* tack x : alpha,
        name: "(T-WeakVar)")) $
    В любом случае окажемся в ситуации когда нельзя применить никакое правило, потому сразу теряем $alpha^*$.
  3. Аналогично, остается $x^alpha$ в контексте, но не можем вывести $alpha : *$.
    $ prooftree(
        rule(
          rule(
            rule(chevron.l chevron.r tack * : square, name: "(T-Axiom)"),
            rule(chevron.l chevron.r tack alpha : *, name: #text(red)[?]),
            x^alpha tack * : square,
            name: "(T-WeakVar)"
          ), 
          x^alpha"," alpha^* tack alpha : *,
          name: "(T-Ini)")
      ) $
]
