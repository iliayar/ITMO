#import "/other/typst/practice_mse.typ": *

// FIXME(iliayar): better spaces for lambda terms
#let term(name) = [#math.class("unary", text(name)) #math.thin]
#let var(name) = [#math.class("unary", name) #math.thin]
#let lam(..vars) = [$lambda$ #h(0pt) #vars.at(0) .]

// TODO(iliayar): Get rid of this thin
// $
//   lam(x) var(x) (term("gg") (term("g") 3)) thin 2
// $
