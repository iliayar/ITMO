module Pair = struct
    (* Sorry for using struct, small hack. forall quantifier only in fields *)
    type ('a, 'b) t = { f : 'r. ('a -> 'b -> 'r) -> 'r }

    let make_pair : 'a -> 'b -> ('a, 'b) t = fun a b -> { f = fun f -> f a b }
    let fst : ('a, 'b) t -> 'a = fun p -> p.f (fun a b -> a)
    let snd : ('a, 'b) t -> 'b = fun p -> p.f (fun a b -> b)
end

module Church = struct
    (* Same here *)
    type t = { f : 'a. ('a -> 'a) -> 'a -> 'a }

    let zero : t = { f = fun s z -> z }
    let succ : t -> t = fun n -> { f = (fun s z -> s @@ n.f s z) }

    let rec of_int = function
    | 0 -> zero
    | n -> succ @@ of_int @@ n - 1

    let to_int n = n.f Int.succ 0
end

module Cat : sig
    type t

    val make_cat : string -> int -> t
    val name : t -> string
    val meowness : t -> int
    val scratch : t -> t
end = struct
    open Pair
    open Church

    type t = (string, Church.t) Pair.t

    let make_cat_impl name meowness : t = 
        make_pair name @@ meowness

    let meowness_impl (cat : t) : Church.t = snd cat

    let make_cat name (meowness : int) : t = 
        make_cat_impl name @@ of_int meowness

    let name (cat : t) : string =
        fst cat

    let meowness (cat : t) : int =
        to_int @@ meowness_impl cat

    let scratch (cat) : t =
        let n = name cat in
        make_cat_impl n (succ @@ meowness_impl cat)
end

let main = 
    (* Check Church numerals *)
    assert Church.(2 = to_int @@ succ @@ succ @@ zero);
    assert Church.(10 = to_int @@ of_int 10);

    (* Check Pair *)
    assert Pair.(1 = fst @@ make_pair 1 2);
    assert Pair.(2 = snd @@ make_pair 1 2);

    (* Check cat *)
    let cat = Cat.make_cat "barsik" 2 in
    assert Cat.("barsik" = name cat);
    assert Cat.(2 = meowness cat);
    let cat = Cat.scratch cat in
    assert Cat.("barsik" = name cat);
    assert Cat.(3 = meowness cat);
