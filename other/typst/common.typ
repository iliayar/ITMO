#import "@preview/tablex:0.0.9": *
#import "@preview/lovelace:0.3.0": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.4.0": canvas, draw

#let lemma = thmbox("lemma", "Лемма")
#let theorem = thmbox("theorem", "Теорема")

#let proof = thmproof("proof", [_Доказательство_])

#let corollary_of = base => thmbox("corollary", [_Следствие_]).with(base: base)
#let corollary_def = corollary_of("definition")
#let corollary_lemma = corollary_of("lemma")
#let corollary = corollary_of("theorem")

#let definition = thmbox("definition", "Определение")
#let symb = thmplain("symbol", [*Обозначение*]).with(numbering: none)

#let example = thmplain("example", "Пример").with(numbering: none)
#let remark = thmbox("remark", [_Примечание_]).with(numbering: none, inset: (x: 1em))
#let task = thmbox("task", [_Задача_])
#let solution = thmplain("solution", [*Решение*]).with(numbering: none, base: "task")
#let statement = thmplain("statement", [*Утверждение*])

#let todo = (note: none) => [#rect(stroke: red)[#text(fill: red, [*Доделать*])]]

#let web_link(url, content) = [ #underline(link(url, content))#super(emoji.chain) ]

#let setup_common(doc) = {

show: thmrules
show link: it => [ #text(blue)[#it] ]

doc

}
