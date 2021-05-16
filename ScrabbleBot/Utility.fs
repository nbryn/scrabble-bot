namespace nbryn

open ScrabbleUtil
module internal Utility =


    let memoize fn =
      let cache = new System.Collections.Generic.Dictionary<_,_>()
      (fun s c ->
        match cache.TryGetValue c with
        | true, v  -> v
        | false, _ -> let v = fn s c
                      cache.Add(c,v)
                      v)

    let rec removeFirst pred lst =
        match lst with
        | h::t when pred h -> t
        | h::t -> h::removeFirst pred t
        | _ -> []

    let removeEmpty (l : list<option<'a>>) = 
        l |> List.filter (fun x -> x.IsSome) |> List.map (fun x -> x.Value) 
          |> List.filter (fun x -> not (Map.isEmpty x))
    
    let appender word append = word@append
    let prepender word prepend = prepend@word


    

    let foldHelper3 map1 map2  =
        Map.fold (fun acc key value -> Map.add key value acc) map1 map2
module internal BoardUtil =
    open Utility
    open Types

    let incrementXTimes amount coord  : coord = (fst coord + amount, snd coord)
    let decrementXTimes amount coord  : coord = (fst coord - amount, snd coord)
    let incrementYTimes amount coord : coord = (fst coord, snd coord + amount)
    let decrementYTimes amount coord : coord = (fst coord, snd coord - amount)

    let incrementX c : coord  = incrementXTimes 1 c
    let decrementX c : coord  = decrementXTimes 1 c
    let incrementY c : coord  = incrementYTimes 1 c
    let decrementY c : coord  = decrementYTimes 1 c

    let squareExist (st : State) (coord : coord) =
        match st.board.squares coord with
        | Some _ -> true
        | None   -> false

    let memSquareExists = memoize squareExist

    let squareFree (st : State) (coord : coord) =
        match Map.tryFind coord st.played with
        | Some _ -> false
        | None   -> true

    let squareExistsAndFree (st : State) (coord : coord) =
        memSquareExists st coord && squareFree st coord

    let squareExistsAndFree2 (st : State) (coord : coord) =
        ((memSquareExists st coord), (squareFree st coord))

    let squareExistsAndNotFree (st : State) (coord : coord) =
        memSquareExists st coord && not(squareFree st coord)

    let verticalChecker (st : State) (c : coord) : Surrounding = 
        (memSquareExists st (decrementY c), (squareExistsAndFree st (decrementY c))),(memSquareExists st (incrementY c), (squareExistsAndFree st (incrementY c)))
        

    let horizontalChecker (st : State) (c : coord) : Surrounding = 
        (memSquareExists st (decrementX c), (squareExistsAndFree st (decrementX c))),(memSquareExists st (incrementX c), (squareExistsAndFree st (incrementX c)))

        
    let wordExists (st : State) (list : List<coord*(char*int)>) =
        let word = List.map (fun (_, (y, _)) -> y) list |> List.toArray |> System.String
        Dictionary.lookup word st.dict

    let wordExists2 (st : State) (list : List<coord*(uint32*(char*int))>) =
        let word = List.map (fun (_,(_,(y, _))) -> y) list |> List.toArray |> System.String
        Dictionary.lookup word st.dict

    let calcPoints (st : State) (word : List<coord*(char*int)>) =
        List.filter (fun x -> squareFree st (fst x)) word
         |> List.map (fun x -> st.board.squares (fst x) |> fun t -> t.Value) 
         |> List.mapi (fun i square -> Map.toList square |> fun x -> List.map (fun (priority, stm) -> (priority, stm (List.map (fun x -> snd x) word) i)) x)
         |> List.fold (fun list n -> List.append n list) []
         |> List.sortBy (fst)
         |> List.map (snd)
         |> List.fold (( >> )) (id)
         |> fun x -> x 0
         |> fun t -> List.fold (fun acc ele -> acc + (snd (snd ele))) t (List.filter (fun x -> not (squareFree st (fst x))) word)
         |> fun m -> if (List.filter (fun x -> squareFree st (fst x)) word).Length = 7 then m + 50 else m


    let calcPoints2 (st : State) (word : List<coord*(uint32*(char*int))>) =
        word |> List.map (fun x -> st.board.squares (fst x) |> fun t -> t.Value) 
             |> List.mapi (fun i square -> Map.toList square |> fun x -> List.map (fun (priority, stm) -> (priority, stm (List.map (fun x -> snd (snd x)) word) i)) x)
             |> List.fold (fun list n -> List.append n list) []
             |> List.sortBy (fst)
             |> List.map (snd)
             |> List.fold (( >> )) (id)
             |> fun x -> x 0
             |> fun m -> if word.Length = 7 then m + 50 else m