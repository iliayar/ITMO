open System

let main =
    let s = Console.ReadLine()

    let cmp i j =
        let mutable k = 0

        while max i j + k < s.Length && s[i + k] = s[j + k] do
            k <- k + 1

        if max i j + k = s.Length then
            if i < j then 1
            else if i = j then 0
            else -1
        else if s[i + k] < s[j + k] then
            -1
        else if s[i + k] = s[j + k] then
            0
        else
            1

    let res = List.sortWith cmp (List.init s.Length id)
    printfn "%s" (String.concat " " (List.map (fun i -> string (i + 1)) res))
