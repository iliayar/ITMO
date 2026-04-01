#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 7],
  date: [25 марта],
  number: 6,
  author: "Ярошевский Илья",
  doc
)

#let Vdash = $⊩$

#task(numbering: (..) => numbering("1", 1))[
  $ prooftree(rule(Gamma"," alpha^* Vdash B : *_w , Gamma Vdash forall alpha. med B : *_w)) quad
    prooftree(rule(Gamma Vdash B : *_-> , Gamma Vdash med B : *_w)) \
    prooftree(rule(Gamma Vdash A : *_->, Gamma Vdash B : *_->, Gamma Vdash A -> B : *_->)) quad
    prooftree(rule(alpha^* in Gamma, Gamma Vdash alpha : *_->)) \
    prooftree(rule(Gamma Vdash B : *_w , Gamma Vdash med B : *))
  $
]
