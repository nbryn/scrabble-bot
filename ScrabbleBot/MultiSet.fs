
module internal MultiSet

        type MultiSet<'a> when 'a : comparison =
            | M of Map<'a, uint32>
            override q.ToString() =
                let (M m) = q

                let s =
                    Map.fold (fun state key value -> sprintf "%s(%A, #%d), " state key value) "" m

                "{" + s.Substring(0, s.Length - 2) + "}"


        let empty = M(Map.empty)

        let size (M s) =
            Map.fold (fun state key value -> state + value) 0u s

        let isEmpty (M s) = size (M s) = 0u

        let contains a (M s) = Map.containsKey a s

        let numItems a (M s) =
            if contains a (M s) then
                Map.find a s
            else
                (0u)

        let add a n (M s) =
            if contains a (M s) then
                let currVal = Map.find a s
                Map.remove a s |> Map.add a (currVal + n) |> M
            else
                M(Map.add a n s)

        let addSingle a (M s) = add a (uint32 1) (M s)

        let remove a (n: uint32) (M s) =
            if contains a (M s) then
                Map.find a s
                |> fun x ->
                    let map = M(Map.remove a s)
                    let newVal = (int (x - n))

                    if newVal <= 0 then
                        map
                    else
                        add a (uint32 newVal) map
            else
                (M s)

        let removeSingle a (M s) = remove a (uint32 1) (M s)

        let fold f acc (M s) =
            Map.fold (fun acc ele x -> f acc ele x) acc s

        let foldBack f (M s) acc =
            Map.foldBack (fun ele x acc -> f ele x acc) s acc

        let map f (M s) =
            Map.toList s
            |> List.map (fun x -> (f (fst x), snd x))
            |> List.fold (fun acc ele -> add (fst ele) (snd ele) acc) empty

        let ofList (lst: 'a List) =
            List.fold (fun acc ele -> addSingle ele acc) empty lst

        let toList (M s) =
            Map.fold (fun acc ele x -> List.replicate (int x) ele :: acc) [] s
            |> List.concat
            |> List.rev

        let union (M s1) (M s2) =
            fold
                (fun state key value ->
                    if contains key (M s2) then
                        Map.find key s2
                        |> fun x ->
                            if x > value then
                                add key x state
                            else
                                state
                    else
                        state)
                (M s1)
                (M s2)

        let sum (M s1) (M s2) =
            fold (fun set ele count -> add ele count set) (M s1) (M s2)


        let subtract (M s1) (M s2) =
            fold (fun state key _ -> remove key (Map.find key s2) state) (M s1) (M s2)


        let intersection (M s1) (M s2) =
            fold
                (fun state key _ ->
                    if contains key (M s2) then
                        Map.find key s2 |> fun x -> add key x state
                    else
                        state)
                empty
                (M s1)
