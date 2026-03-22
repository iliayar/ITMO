#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 6],
  date: [18 марта],
  number: 6,
  author: "Ярошевский Илья",
  doc
)

#let Boo = [`Bool`]
#let Top = [`Top`]
#let Bot = $perp$
#let fi = name => raw(name)

#task(numbering: (..) => numbering("1", 1))[
  1.
    $ {fi("la") : Boo, fi("lb") : Boo} union {fi("lb") : Boo, fi("lc") : Boo} & = {fi("lb") : Boo} \
      {fi("la") : Boo, fi("lb") : Boo} inter {fi("lb") : Boo, fi("lc") : Boo} & = {fi("la") : Boo, fi("lb") : Boo, fi("lc") : Boo}
    $
  2. 
    $ {fi("la") : Boo, fi("lb") : {}} union {fi("lb") : Boo, fi("lc") : Boo} & = {fi("lb") : Top} \
      {fi("la") : Boo, fi("lb") : {}} inter {fi("lb") : Boo, fi("lc") : Boo} & = {fi("la") : Boo, fi("lb") : {} inter Boo, fi("lc") : Boo}
    $
    Пересечения не существует, т.к. ${} inter Boo$ не существует. Но если есть bottom, то
    $ {fi("la") : Boo, fi("lb") : {}} inter {fi("lb") : Boo, fi("lc") : Boo} & = {fi("la") : Boo, fi("lb") : Bot, fi("lc") : Boo} 
    $
  3. 
    $ Boo union (Boo -> Boo) & = Top \
      Boo inter (Boo -> Boo) & = Bot
    $
  4. 
    $ (Boo -> Boo) union (Boo -> (Boo -> Boo)) & = Boo -> Top \
      (Boo -> Boo) inter (Boo -> (Boo -> Boo)) & = Boo -> (Boo inter (Boo -> Boo)) = Boo -> Bot
    $
  5.
    $ ({ fi("la") : Boo, fi("lb") : Boo} -> Boo) union ({ fi("lb") : Boo, fi("lc") : Boo} -> Boo) = \
       = ({ fi("la") : Boo, fi("lb") : Boo, fi("lc") : Boo} -> Boo)
    $
    $ ({ fi("la") : Boo, fi("lb") : Boo} -> Boo) inter ({ fi("lb") : Boo, fi("lc") : Boo} -> Boo) = ({ fi("lb") : Boo} -> Boo)
    $
]
