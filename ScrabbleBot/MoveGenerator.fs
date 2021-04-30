namespace nbryn
open Parser
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

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

    let squareExistsAndFree2 (st : State) (coord : coord) =
        ((squareExist st coord), (squareFree st coord))

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

    let appender word charToAppend = word@[charToAppend]
    let prepender word charToAppend = [charToAppend]@word

    let collectWord coordAdjuster concat (st : State) (word : List<coord*(uint32*(char*int))>)  =
        let rec go word c =
            if   squareExistsAndNotFree st c
            then go (concat word (c, (Map.find c st.played))) (coordAdjuster c)                
            else word

        go word (coordAdjuster (fst word.[0]))

    let collectWordXInc = collectWord incrementX appender
    let collectWordXDec = collectWord decrementX prepender
    let collectWordYInc = collectWord incrementY appender
    let collectWordYDec = collectWord decrementY prepender

    // Calc points
    let checkVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match verticalChecker st c with
       | ((_,true),(_,true))         -> true
       | ((false,_),(false,_))       -> false  
       | ((_,true),(false,_))        -> true
       | ((false,_),(true,false))    -> wordExists st (collectWordYInc st word)
       | ((_,true),(true,false))     -> wordExists st (collectWordYInc st word)
       | ((true,false),(true,false)) -> let first = collectWordYInc st word
                                        wordExists st (first.[0..first.Length-2] @ collectWordYDec st word)
       | ((true,false),(false,_))    -> wordExists st (collectWordYDec st word)
       | ((true,false),(_,_))        -> wordExists st (collectWordYDec st word)
       | (_,(true,_))                -> true 
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match horizontalChecker st c with
       | ((_,true),(_,true))         -> true
       | ((false,_),(_,_))           -> false 
       | ((_,true),(false,_))        -> true 
       | ((_,true),(true,false))     -> wordExists st (collectWordXInc st word)
       | ((true,false),(true,false)) -> let first = collectWordXInc st word
                                        wordExists st (first.[0..first.Length-2] @ collectWordXDec st word)
       | ((true,false),(false,_))    -> wordExists st (collectWordXDec st word)
       | ((true,false),(_,_))        -> wordExists st (collectWordXDec st word)
 

    let getChar (s : (coord*(uint32*(char*int)))) = fst (snd((snd s)))

    let calcPoint (l : List<coord*(uint32*(char*int))>) = List.fold (fun acc (x, (y, (z,x))) -> acc + x) 0 l

    let rec stepDictWordExists (word : List<coord*(uint32*(char*int))>) (dict : Dictionary.Dict) =
            if List.isEmpty word then dict
            else stepDictWordExists (word.[1..word.Length-1]) (snd ((Dictionary.step (getChar word.[0]) dict).Value))

    // Use special checker for  
    let check1 collector coordAdjuster state coord word =
        match squareExistsAndFree2 state (coordAdjuster coord) with
        | (_,true)      -> true
        | (false,false) -> false
        | (true,false)  -> wordExists state (collector state word)

    let check1XDec = check1 collectWordXDec decrementX
    let check1XInc = check1 collectWordXInc incrementX
    let check1YDec = check1 collectWordYDec decrementY
    let check1YInc = check1 collectWordYInc incrementY

    // Mathc checdkHorizontal with -> include points
    // Check horizontal on vertical and vice verce - Start from -/+1 and collect words
    // If last move failed - Don't play again
    // Merge checker and check1?
    // Look ahead does not work
    // Merge all checkers in one function?
    let findValidWords coordAdjuster checker check1 concat (st : State) coord startingPoint   =
        let rec go hand word existing c words =
            hand |> List.fold (fun x k -> let charr = Map.find k st.tiles
                                          let newWord     = concat word (c, (k, charr)) 
                                          let newExisting = concat existing  (c, (k, charr)) 
                                          if (not (checker st c [(c, (k, charr))]) || not (check1 st c newExisting))
                                          then words
                                          else                           
                                          if  wordExists st newExisting
                                          then Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) (Map.add (calcPoint newWord) newWord words)) x 
                                          else Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) words) x
                                          
                             ) words

        go (MultiSet.toList st.hand) [] startingPoint coord Map.empty


    let findValidWordsXInc = findValidWords incrementX checkVertical check1XInc appender
    let findValidWordsXDec = findValidWords decrementX checkVertical check1XDec prepender
    let findValidWordsYInc = findValidWords incrementY checkHorizontal check1YInc appender
    let findValidWordsYDec = findValidWords decrementY checkHorizontal check1YDec prepender

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
                                   then Some (findValidWordsXInc st (fst first) [])
                                   else
                                   findValidWordsXInc st (incrementX (fst first)) [first]
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsXDec st (decrementX (fst first)) [first]))
                            
       | ((_,true), (_,_))      -> Some (findValidWordsXDec st (decrementX (fst first)) (collectWordXInc st [first]))
      
       | ((_,_), (_,true))      -> let existingWord = collectWordXDec st [first]          
                                   Some (findValidWordsXDec st (decrementXTimes (fst first) existingWord.Length) existingWord)

                            
    let tryVertical (st : State) (first : coord*(uint32*(char*int))) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> if st.turns = 0 
                                   then Some (findValidWordsYInc st (fst first) [])
                                   else
                                   findValidWordsYInc st (incrementY (fst first)) [first]
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsYDec st (decrementY (fst first)) [first]))
               
       | ((_,true), (_,_))    -> let existingWord = collectWordYInc st [first]          
                                 Some (findValidWordsYDec st (decrementYTimes (fst first) existingWord.Length) existingWord)

       | ((_,_), (_,true))    -> Some (findValidWordsYInc st (incrementY (fst first)) (collectWordYDec st [first]))

    let collectWords (st : State) =
        st.played |> Map.toList |> List.map (fun coord -> tryHorizontal st coord) 
                  |> fun x -> (List.map (fun coord -> tryVertical st coord) (Map.toList st.played)) @ x

    let wordOnBoard (st : State) word = word |> List.forall (fun x -> squareExistsAndFree st (fst x))

    let extractResult (st : State) (l : list<Map<int,list<coord * (uint32 * (char * int))>>>) =
        l |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
          |> Map.toList |> List.filter (fun (_, x) -> wordOnBoard st x) 
          |> fun x -> snd (Seq.maxBy fst x)

    // Add prefix and postfix
    // Length x width
    // Write horizontal after checking vertical 
    let findMove (st : State) = 
        collectWords st |> List.filter (fun x -> x.IsSome) |> List.map (fun x -> x.Value) |> List.filter (fun x -> not (Map.isEmpty x))
        |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList st.hand) else SMPlay (extractResult st x)
                      
    let convertState b d pn h p t tu = {board = b; dict = d; playerNumber = pn; hand = h; played = p; tiles = t; turns = tu}
