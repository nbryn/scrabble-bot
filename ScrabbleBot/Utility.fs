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


    let incOrDec amount c adjuster x =
        match x with
        | true -> adjuster amount c
        | _   -> decrementXTimes amount c
    
    let incOrDecY amount c inc =
        match inc with
        | true -> incrementYTimes amount c
        | _   -> decrementYTimes amount c

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
