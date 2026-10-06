module State = struct
    type t = (string * int) list

    let empty = []
    let eval st x = List.assoc x st
    let bind st x v = (x, v) :: st
end

module Expr = struct
    type t =
    | Var of string
    | Const of int
    | Div of t * t
    | Mod of t * t
    | Mul of t * t
    | Eq of t * t
    | Le of t * t
    | Gt of t * t

    let rec eval st = function
    | Var x -> State.eval st x
    | Const n -> n
    | Div (l, r) -> (eval st l) / (eval st r)
    | Mod (l, r) -> (eval st l) mod (eval st r)
    | Mul (l, r) -> (eval st l) * (eval st r)
    | Eq (l, r) -> if (eval st l) = (eval st r) then 1 else 0
    | Le (l, r) -> if (eval st l) <= (eval st r) then 1 else 0
    | Gt (l, r) -> if (eval st l) > (eval st r) then 1 else 0
end

module Stmt = struct
    type t =
    | Skip
    | Assn of string * Expr.t
    | Seq of t * t
    | ITE of Expr.t * t * t
    | While of Expr.t * t

    let rec eval st = function
    | Skip -> st
    | Assn (x, e) -> State.bind st x (Expr.eval st e)
    | Seq (l, r) -> eval (eval st l) r
    | ITE (c, t, e) -> eval st (if Expr.eval st c = 0 then e else t)
    | While (c, b) as w -> 
        if Expr.eval st c = 0 
        then st
        else eval (eval st b) w
end

module Emb = struct
    let whil c b = Stmt.While (c, b)
    let ite c t e = Stmt.ITE (c, t, e)
    let (>>) l r = Stmt.Seq (l, r)
    let skip = Stmt.Skip
    let (<<=) x e = Stmt.Assn (x, e)

    let var x = Expr.Var x
    let const x = Expr.Const x

    let ( * ) l r = Expr.Mul (l, r)
    let ( / ) l r = Expr.Div (l, r)
    let ( mod ) l r = Expr.Mod (l, r)
    let ( == ) l r = Expr.Eq (l, r)
    let ( <= ) l r = Expr.Le (l, r)
    let ( > ) l r = Expr.Gt (l, r)

    let degree = 
        ("d" <<= const 1)
        >> (whil ((var "k") > (const 0)) (
            (ite ((var "k") mod (const 2) == (const 1))
                ("d" <<= (var "d") * (var "n"))
                (skip)
            )
            >> ("n" <<= var "n" * var "n")
            >> ("k" <<= var "k" / const 2)
        ))

end

let main = 
    let res = Stmt.eval (State.bind (State.bind State.empty "n" 3) "k" 5) Emb.degree in
    print_endline @@  Int.to_string @@ State.eval res "d"
