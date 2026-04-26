#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 11],
  date: [22 апреля],
  number: 11,
  author: "Ярошевский Илья",
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  $ lambda p^(Pi a^A. Pi b^A. R med a med b -> R med b med a -> bot). med lambda a^A. med lambda r^(R med a med a). med p med a med a med r med r $
]

#task(numbering: (..) => numbering("1", 2))[
  - $A^*, Q^(A -> *), P^(A -> *) tack med ? : (Pi a^A. med Q med a) -> (Pi b^A. med P med b -> Q med b) $
    $ ? = lambda "p"^(Pi a^A. Q med a). med lambda b^A. med lambda "_"^(P med b). med p med b $
  - $A^*, P^(A -> *), Q^(A -> *) tack med ? : (Pi a^A. P med a -> Q med a) -> (Pi b^A. P med b) -> (Pi c^A. Q med c)$
    $ ? = lambda p^(Pi a^A. P med a -> Q med a). med lambda r^(Pi b^A. P med b). med lambda c^A. med p med c med (r med c) $
]
