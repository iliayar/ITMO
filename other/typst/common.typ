#import "@preview/tablex:0.0.8": *
#import "@preview/lovelace:0.3.0": *
#import "@preview/ctheorems:1.1.0": *

#let lemma = thmbox("lemma", "Лемма")
#let theorem = thmbox("theorem", "Теорема")

#let corollary_of = base => thmbox("corollary", [_Следствие_]).with(base: base)
#let corollary_lemma = corollary_of("lemma")
#let corollary = corollary_of("theorem")

#let definition = thmbox("definition", "Определение")

#let example = thmplain("example", "Пример").with(numbering: none)
#let remark = thmbox("remark", [_Примечание_]).with(numbering: none)
#let task = thmbox("task", [_Задача_])
#let solution = thmplain("solution", [*Решение*]).with(numbering: none, base: "task")

#let todo = () => [#rect(stroke: red)[#text(fill: red, [*Доделать*])]]

#let setup_common(doc) = {

set heading(numbering: "1.")

show: thmrules

doc

}
