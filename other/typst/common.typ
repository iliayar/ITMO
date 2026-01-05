#import "@preview/tablex:0.0.9": *
#import "@preview/lovelace:0.3.0": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.4.0": canvas, draw
#import "@preview/pinit:0.2.2": *

#let lemma = thmbox("lemma", "Лемма")
#let theorem = thmbox("theorem", "Теорема")

#let proof = thmproof("proof", [Доказательство])

#let corollary_of = base => thmplain("corollary", [_Следствие_]).with(base: base)
#let corollary_def = corollary_of("definition")
#let corollary_lemma = corollary_of("lemma")
#let corollary_statement = corollary_of("statement")
#let corollary = corollary_of("theorem")

#let definition = thmbox("definition", "Определение")
#let symb = thmplain("symbol", [*Обозначение*]).with(numbering: none)

#let example = thmplain("example", "Пример").with(numbering: none)
#let remark = thmplain("remark", [#underline[Примечание]]).with(numbering: none, inset: (x: 1em))
#let properties = thmplain("remark", [*Свойство*]).with(numbering: none, inset: (x: 1em))
#let task = thmbox("task", [Задача])
#let solution = thmplain("solution", [*Решение*]).with(numbering: none, base: "task")
#let statement = thmplain("statement", [*Утверждение*])

#let todo = (note: none) => [#box(stroke: red, inset: 4pt, baseline: 4pt)[#text(fill: red, [*Доделать*])]]
#let fixme = (note: none) => [#box(stroke: orange, inset: 4pt, baseline: 4pt)[#text(fill: orange, [*Но это не точно*])]]

#let web_link(url, content) = [ #underline(link(url, content))#super(emoji.chain) ]

#let xunderline(stroke: black, equation) = block(
  stroke: (bottom: .5pt + stroke), 
  outset: (bottom: 1.5pt), 
  $ equation $
)

#let setup_common(doc) = {

show: thmrules
show link: it => [ #text(blue)[#it] ]

show raw: it => {
  show regex("pin\d"): it => pin(eval(it.text.slice(3)))
  it
}

doc

}
