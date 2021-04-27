namespace nbryn
open Parser
open ScrabbleUtil

module internal MoveGenerator =
  
    type State = {
        board         : Parser.board
        dict          : Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, (uint32*(char*int))>
        tiles         : Map<uint32, char*int>
        turns         : int
    }

    type Surrounding = (bool*bool)*(bool*bool)

    let incrementX (c : coord) : coord  = (fst c + 1, snd c)
    let decrementX (c : coord) : coord  = (fst c - 1, snd c)
    let incrementY (c : coord) : coord  = (fst c, snd c + 1)
    let decrementY (c : coord) : coord  = (fst c, snd c - 1)

    let incrementXTimes (c : coord) (amount : int) : coord = (fst c + amount, snd c)
    let decrementXTimes (c : coord) (amount : int) : coord = (fst c - amount, snd c)

    let incrementYTimes (c : coord) (amount : int) : coord = (fst c + amount, snd c)
    let decrementYTimes (c : coord) (amount : int) : coord = (fst c - amount, snd c)
        
    // Need to look at function from map
    let squareExist (st : State) (coord : coord) =
        ((fst coord) < 8 && (fst coord) > -8) && ((snd coord) < 8 && (snd coord) > -8)

    let squareFree (st : State) (coord : coord) =
        match Map.tryFind coord st.played with
        | Some _ -> false
        | None   -> true

    let squareExistsAndFree (st : State) (coord : coord) =
        squareExist st coord && squareFree st coord

    let squareExistsAndNotFree (st : State) (coord : coord) =
        squareExist st coord && not(squareFree st coord)

    let verticalChecker (st : State) (c : coord) : Surrounding = 
        (squareExist st (decrementY c), (squareExistsAndFree st (decrementY c))),(squareExist st (incrementY c), (squareExistsAndFree st (incrementY c)))
        

    let horizontalChecker (st : State) (c : coord) : Surrounding = 
        (squareExist st (decrementX c), (squareExistsAndFree st (decrementX c))),(squareExist st (incrementX c), (squareExistsAndFree st (incrementX c)))

    let rec removeFirst pred lst =
        match lst with
        | h::t when pred h -> t
        | h::t -> h::removeFirst pred t
        | _ -> []
        
    let wordExists (st : State) (list : List<coord*(uint32*(char*int))>) =
        let word = List.map (fun (m, (x, (y, z))) -> y) list |> List.toArray |> System.String
        Dictionary.lookup word st.dict

    let getVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go st c word =
            let newCoord = if increment then incrementY c else decrementY c
            if squareExistsAndNotFree st newCoord
            then Map.find newCoord st.played 
                 |> fun x -> if increment then [(newCoord, (fst x, snd x))]@word else word@[(newCoord, (fst x, snd x))]
                 |> go st newCoord
            
            else word

        go st c word

    let getHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go st c word =    
            let newCoord = if increment then incrementX c else decrementX c
            if squareExistsAndNotFree st newCoord
            then Map.find newCoord st.played 
                 |> fun x -> if increment then word@[(newCoord, (fst x, snd x))] else [(newCoord, (fst x, snd x))]@word
                 |> go st newCoord
            
            else word

        go st c word

    // Calc points
    let checkVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match verticalChecker st c with
       | ((_,true), (_,true))         -> true
       | ((false,_), (false,_))       -> false  
       | ((_,true), (false,_))        -> true
       | ((_,true), (true,false))     -> wordExists st (getVertical st c word true)
       | ((true,false), (true,false)) -> let first = getVertical st c word true
                                         wordExists st (first.[0..first.Length-2] @ getVertical st c word false)
       | ((true,false), (false,_))    -> wordExists st (getVertical st c word false)
       | ((true,false), (_,_))        -> wordExists st (getVertical st c word false)
       | (_,(true,_))                 -> true 
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match horizontalChecker st c with
       | ((_,true), (_,true))         -> true
       | ((false,_), (_,_))           -> false 
       | ((_,true), (false,_))        -> true 
       | ((_,true), (true,false))     -> wordExists st (getHorizontal st c word true)
       | ((true,false), (true,false)) -> let first = getHorizontal st c word true
                                         wordExists st (first.[0..first.Length-2] @ getHorizontal st c word false)
       | ((true,false), (false,_))    -> wordExists st (getHorizontal st c word false)
       | ((true,false), (_,_))        -> wordExists st (getHorizontal st c word false)


    let getChar (s : (coord*(uint32*(char*int)))) = fst (snd((snd s)))

    let calcPoint (l : List<coord*(uint32*(char*int))>) = List.fold (fun acc (x, (y, (z,x))) -> acc + x) 0 l

    let rec stepDictWordExists (word : List<coord*(uint32*(char*int))>) (dict : Dictionary.Dict) =
            if List.isEmpty word then dict
            else stepDictWordExists (word.[1..word.Length-1]) (snd ((Dictionary.step (getChar word.[0]) dict).Value))


    let collectWord (st : State) (first : coord*(uint32*(char*int))) coordAdjuster append =
        let rec go word c =
            if   squareExistsAndNotFree st c
            then let newWord = if append then [c, (Map.find c st.played)]@word else word@[c, (Map.find c st.played)]
                 go newWord (coordAdjuster c)                
            else word

        go [first] (coordAdjuster (fst first))


    // Mathc checdkHorizontal with -> include points
    // Dont check vertical on first
    let findValidWords (st : State) coord startingPoint coordAdjuster checker append =
        let rec go hand word existing c words =
            if not (squareExist st (coordAdjuster c)) then words
            else
            hand |> List.fold (fun x k -> let charr = Map.find k st.tiles
                                          if not (checker st c [(c, (k, charr))]) then words
                                          else 
                                          let newWord     = if append then [(c, (k, charr))]@word else word@[(c, (k, charr))]
                                          let newExisting = if append then [(c, (k, charr))]@existing else existing@[(c, (k, charr))]                                
                                          if  wordExists st newExisting
                                          then Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) (Map.add (calcPoint newWord) newWord words)) x 
                                          else Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) words) x
                                          
                             ) words

        go (MultiSet.toList st.hand) [] startingPoint coord Map.empty


    // Include point from all words -> include points from squares
    // Try place word before, after & in middle
    // Check in front of curren tile - Eg checkHorizontal on Horizontal placement not only vertical
    // Change tiles if no options
    let tryHorizontal (st : State) (first : coord*(uint32*(char*int))) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       // Problems with placing tiles on occupied square
       | ((_,true), (_,true))   -> if st.turns = 0 
                                   then Some (findValidWords st (fst first) [] incrementX checkVertical false)
                                   else
                                   findValidWords st (incrementX (fst first)) [first] incrementX checkVertical false
                                   |> fun x -> Some (Map.fold (fun acc key value -> Map.add key value acc) x (findValidWords st (decrementX (fst first)) [first] decrementX checkVertical true))
                            
       | ((_,true), (_,_))      -> let existingWord = collectWord st first incrementX false
                                   Some (findValidWords st (decrementX (fst first)) existingWord decrementX checkVertical true)
      
       | ((_,_), (_,true))      -> let existingWord = collectWord st first decrementX false          
                                   Some (findValidWords st (decrementXTimes (fst first) existingWord.Length) existingWord decrementX checkVertical true)

                            
    let tryVertical (st : State) (first : coord*(uint32*(char*int))) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> if st.turns = 0 
                                   then Some (findValidWords st (fst first) [] incrementY checkHorizontal false)
                                   else
                                   findValidWords st (incrementY (fst first)) [first] incrementY checkHorizontal false
                                   |> fun x -> Some (Map.fold (fun acc key value -> Map.add key value acc) x (findValidWords st (decrementY (fst first)) [first] decrementY checkHorizontal true))
               
       | ((_,true), (_,_))    -> let existingWord = collectWord st first incrementY false          
                                 Some (findValidWords st (decrementYTimes (fst first) existingWord.Length) existingWord decrementY checkHorizontal true)

       | ((_,_), (_,true))    -> let existingWord = collectWord st first decrementY true
                                 Some (findValidWords st (incrementY (fst first)) existingWord incrementY checkHorizontal false)

    let collectWords (st : State) =
        st.played |> Map.toList |> List.map (fun coord -> tryHorizontal st coord) 
                  |> fun x -> (List.map (fun coord -> tryVertical st coord) (Map.toList st.played)) @ x

    let wordOnBoard (st : State) word = word |> List.forall (fun x -> squareExist st (fst x))

    let extractResult (st : State) (l : list<option<Map<int,list<coord * (uint32 * (char * int))>>>>) =
        l |> List.filter (fun x -> x.IsSome) |> List.map (fun x -> x.Value)
          |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
          |> Map.toList |> List.filter (fun (_, x) -> ((wordExists st x) && (wordOnBoard st x))) 
          |> fun x -> snd (Seq.maxBy fst x)

    // Add prefix and postfix
    // Length x width
    // Write horizontal on top of horizontal 
    let findMove (st : State) = collectWords st |> extractResult st
                      
    let convertState b d pn h p t tu = {board = b; dict = d; playerNumber = pn; hand = h; played = p; tiles = t; turns = tu}
