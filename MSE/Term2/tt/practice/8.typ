#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 8],
  date: [1 апреля],
  number: 7,
  author: "Ярошевский Илья",
  doc
)

// #task[
//   1. $bold(S) equiv lambda f med g med x. f med (g med x)$
//     - $Lambda beta med gamma. med \lambda$
// ]

// #task[
//   $ lambda x^bot . med x med (bot -> bot -> bot) med (x med (bot -> bot) med x)^(bot) med (x med (bot -> bot -> bot) med x med x)^bot : bot -> bot $
// ]

// #task[
//   $ x_(n + 1)^bot, dots, x_m^bot $
//   #todo()
// ]

#let Vdash = $⊩$

#task(numbering: (_, ..n) => numbering("1", ..n))[
  По индукции:
  - База:
    $ prooftree(rule(x^bot_(n + 1)"," dots"," x^bot_m"," x_1^bot"," dots"," x_n^bot tack x_i : bot, x^bot_(n + 1)"," dots"," x^bot_m tack lambda x_1^bot dots x_n^bot. med x_i : underbrace(bot -> dots -> bot, n) -> bot)) $
  - Переход:
  $ prooftree(
      rule(
        rule(
          rule(
            rule(
              rule(
                rule(Gamma tack x_i : bot equiv forall alpha. alpha, name: "(T-Var)"),
                rule(
                  rule(dots, Gamma Vdash A_1 equiv bot -> dots -> bot : *),
                  dots,
                  Gamma Vdash A_1 -> dots -> A_k -> bot : *),
                Gamma tack x_i (A_1 -> dots -> A_k -> bot) : A_1 -> dots -> A_k -> bot
              ),
              dots
            ),
            Gamma tack x_i (A_1 -> dots -> A_k -> bot) med M_1 dots M_(k - 1) : A_k -> bot
          ),
          rule(Gamma tack M_k : A_k := bot -> dots -> bot, name: #[(IH)]),
          underbrace(x^bot_(n + 1)"," dots"," x^bot_m"," x_1^bot"," dots"," x_n^bot, Gamma) tack x_i (A_1 -> dots -> A_k -> bot) med M_1 dots M_k : bot
        ),
        x^bot_(n + 1)"," dots"," x^bot_m tack lambda x_1^bot dots x_n^bot. med x_i (A_1 -> dots -> A_k -> bot) med M_1 dots M_k : underbrace(bot -> dots -> bot, n) -> bot)) $
]


// #task(numbering: (_, ..n) => numbering("1", ..n))[
//   1. $beta^*, x^beta tack x : beta$
//   2. $beta^*, x^(beta -> beta) tack x med beta : beta$
//   3. $beta^*, x^(beta -> (beta -> beta) -> beta) tack x med beta : (beta ->beta) -> beta$
//   4. $beta^*, x^bot tack x med ((beta -> beta) -> beta) med (x med (beta -> beta)) : beta$
//   4. $beta^*, x^bot tack x med (beta -> beta) med (x med beta) : beta$
//   5. $beta^*, x^(forall alpha. alpha -> alpha) tack x med (beta -> beta) med (x med beta) : beta -> beta$
//   6. $beta^*, x^(forall alpha. alpha -> alpha -> alpha) tack x med (beta -> beta -> beta) med (x med beta) (x med beta) : beta -> beta -> beta$
// ]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ & #[`if`] && equiv lambda b^(#[`Bool`]) med x^A med y^A. b med A med x med y : #[`Bool`] -> A -> A -> A  \
    & #[`not`] && equiv lambda b^(#[`Bool`]). med b #[`Bool`] med #[`fls`] med #[`tru`] : #[`Bool`] -> #[`Bool`] \
    & #[`not'`] && equiv lambda b^(#[`Bool`]). Lambda alpha. lambda t^alpha med f^alpha. med b med alpha med f med t : #[`Bool`] -> #[`Bool`] \
    & #[`and`] && equiv lambda x^(#[`Bool`]) med y^(#[`Bool`]). med x #[`Bool`] med y med #[`fls`] : #[`Bool`] -> #[`Bool`] -> #[`Bool`] \
    & #[`and'`] && equiv lambda x^(#[`Bool`]) med y^(#[`Bool`]). Lambda alpha. lambda t^alpha f^alpha. med x med alpha med (y med alpha med t med f) med f : #[`Bool`] -> #[`Bool`] -> #[`Bool`]
  $
]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ & #[`mult1`] && equiv lambda m^(#[`Nat`]) med n^(#[`Nat`]). med m med #[`Nat`] med (#[`plus`] med #[`Nat`] med n) med #[`0`] \
    & #[`mult2`] && equiv lambda m^(#[`Nat`]) med n^(#[`Nat`]). Lambda alpha. med s^(alpha -> alpha) med z^alpha. med m med alpha med (n med alpha med s) med z \
    & #[`mult3`] && equiv lambda m^(#[`Nat`]) med n^(#[`Nat`]). Lambda alpha. med s^(alpha -> alpha). med m med alpha med (n med alpha med s)
  $
]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ #[`EitherAB`] equiv forall gamma. (A -> gamma) -> (B -> gamma) -> gamma $
  $ #[`inL`] equiv lambda a^A. Lambda gamma. lambda f^(A -> gamma) med g^(B -> gamma). med f med a : A -> #[`EitherAB`] $
  $ #[`inR`] equiv lambda b^B. Lambda gamma. lambda f^(A -> gamma) med g^(B -> gamma). med g med b : B -> #[`EitherAB`] $
  $ #[`cases`] equiv lambda e^(#[`EitherAB`]). Lambda gamma. lambda f^(A -> gamma) med g^(B -> gamma). med e med gamma med f med g : #[`EitherAB`] -> forall gamma. (A -> gamma) -> (B -> gamma) -> gamma $
  $ #[`cases`] equiv lambda e^#[`EitherAB`]. med e : #[`EitherAB`] -> forall gamma. (A -> gamma) -> (B -> gamma) -> gamma $
]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ #[`ListA`] equiv forall alpha. (A -> alpha -> alpha) -> alpha -> alpha $
  $ #[`cons`] equiv  lambda x^A med l^#[`ListA`]. med Lambda alpha. med lambda f^(A -> alpha -> alpha) med z^alpha. med f med x med (l med alpha med f med z) : A -> #[`ListA`] -> #[`ListA`] $
  $ #[`nil`] equiv Lambda alpha. med lambda f^(A -> alpha -> alpha) med z^alpha. med z : #[`ListA`] $
  $ #[`fold`] equiv lambda l^#[`ListA`]. med l : #[`ListA`] -> forall alpha. (A -> alpha -> alpha) -> alpha -> alpha $
]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ #[`Nat`] equiv forall alpha. (alpha -> alpha) -> alpha -> alpha quad #[`PairAB`] equiv forall alpha. (A -> B -> alpha) -> alpha $
  $ #[`pair`] : A -> B -> #[`PairAB`] quad #[`fst`] : #[`PairAB`] -> A quad #[`snd`] : #[`PairAB`] -> B quad #[`succ`] : #[`Nat`] -> #[`Nat`] $
  $ #[`zp`] equiv #[`pair`] med #[`0`] med #[`0`] : #[`PairNatNat`] $
  $ #[`sp`] equiv lambda p^#[`PairNatNat`]. med #[`pair`] med (#[`snd`] med p) med (#[`succ`] med (#[`snd`] med p)) : #[`PairNatNat`] -> #[`PairNatNat`] $
  $ #[`pred`] equiv lambda m^#[`Nat`]. med #[`fst`] med (m med #[`PairNatNat`] med #[`sp`] med #[`zp`]) : #[`Nat`] -> #[`Nat`] $
]

#task(numbering: (_, ..n) => numbering("1", ..n))[
  $ #[`xz`] equiv med lambda x^A. med #[`pair`] med x med #[`0`] : A -> #[`PairANat`] $
  $ #[`fs`] equiv lambda f^(A -> #[`Nat`] -> A) med p^#[`PairANat`]. med #[`pair`] med (f med (#[`fst`] med p) med (#[`snd`] med p)) med (#[`succ`] med (#[`snd`] med p)) : (A -> #[`Nat`] -> A) -> #[`PairANat`] -> #[`PairANat`] $
  $ #[`rec`] equiv lambda m^#[`Nat`] med f^(A -> #[`Nat`] -> A) med x^A. med #[`fst`] med (m med #[`PairANat`] med (#[`fs`] med f) med (#[`xz`] med x)) : #[`Nat`] -> (A -> #[`Nat`] -> A) -> A -> A $
]
