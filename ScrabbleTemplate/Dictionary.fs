module internal Dictionary

      type Dictionary = D of Map<char, Dictionary> * bool

      let empty () = D (Map.empty, false)

      let private containsWord =
        function
        | D (_, b) -> b

      let insert (s : string) dict = 
                let rec go =
                        function
                        | ([], D (a, _))      -> D    (a, true)
                        | ([x], D (a, b))     -> if   Map.containsKey x a
                                                 then D (Map.add x (go ([], Map.find x a)) a, b) 
                                                 else D (Map.add x (go ([], empty ())) a, b)
                        | (x :: xs), D (a, b) -> if   Map.containsKey x a
                                                 then D (Map.add x (go (xs, Map.find x a)) a, b) 
                                                 else D (Map.add x (go (xs, empty ())) a, b)
                go (Seq.toList s, dict)
        
      let lookup (s : string) dict =
                let rec go =
                        function
                        | ([], D (_, _))      -> false
                        | ([x], D (a, _))     -> if   Map.containsKey x a
                                                 then Map.find x a |> containsWord
                                                 else false
                        | (x :: xs), D (a, _) -> if   Map.containsKey x a
                                                 then go (xs, Map.find x a)
                                                 else false
                go (Seq.toList s, dict)

      let step (c : char) =
                 function
                 | D (a, _) -> if   Map.containsKey c a
                               then Map.find c a |> fun x -> Some (containsWord x, x)
                               else None
               