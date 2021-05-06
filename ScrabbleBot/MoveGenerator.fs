namespace nbryn
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open BoardUtil
open Types
open Utility
module internal MoveGenerator =

    let collectWord coordAdjuster concat (st : State) (word : List<coord*(char*int)>)  =
        let rec go word c p =
            if   not (squareFree st c)
            then go (concat word ([c, (Map.find c st.played)])) (coordAdjuster c) (p + (snd (Map.find c st.played)))              
            else (word,p)

        go word (coordAdjuster (fst word.[0])) 0

    let collectWordXInc = collectWord incrementX appender
    let collectWordXDec = collectWord decrementX prepender
    let collectWordYInc = collectWord incrementY appender
    let collectWordYDec = collectWord decrementY prepender

    let checkWord collector state word =
        let word = collector state word
        ((wordExists state (fst word)), snd word)

    let checkWordXInc = checkWord collectWordXInc
    let checkWordXDec = checkWord collectWordXDec
    let checkWordYInc = checkWord collectWordYInc
    let checkWordYDec = checkWord collectWordYDec

    // Remember merge
    let checkVertical (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match verticalChecker st c with
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(false,_))       -> (false, 0)  
       | ((_,true),(false,_))        -> (true, 0)
       | ((false,_),(true,false))    -> checkWordYInc st word
       | ((_,true),(true,false))     -> checkWordYInc st word
       
       // Error here?
       | ((true,false),(true,false)) -> let first = collectWordYInc st word
                                        let second = collectWordYDec st word
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((true,false),(false,_))    -> checkWordYDec st word
       | ((true,false),(_,_))        -> checkWordYDec st word
       | (_,(true,_))                -> (true, 0)
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match horizontalChecker st c with
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(_,_))           -> (false, 0) 
       | ((_,true),(false,_))        -> (true, 0) 
       | ((_,true),(true,false))     -> checkWordXInc st word

       | ((true,false),(true,false)) -> let first = collectWordXInc st word
                                        let second = collectWordXDec st word
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))

       | ((true,false),(false,_))    -> checkWordXDec st word
       | ((true,false),(_,_))        -> checkWordXDec st word
                                        
 
    let calcPoint (l : List<coord*(uint32*(char*int))>) = List.fold (fun acc (_, (_, (_,x))) -> acc + x) 0 l

    // When incrementing need to check vertical asweel
    let check1 collector coordAdjuster concat state coord word =
        match squareExistsAndFree2 state coord with
        | (true,true)  ->  match squareExistsAndFree2 state (coordAdjuster coord) with
                           | (false,_)    -> (true,0)
                           | (true,true)  -> (true,0) 
                           | (true,false) -> let w = collector state word 
                                             (wordExists state (concat (fst w) word), snd w)
        | (true, false) -> let w = collector state word 
                           if (wordExists state (concat (fst w) word))
                           then match squareExistsAndFree2 state (coordAdjuster coord) with
                                | (false,_)    -> (true, snd w)
                                | (true,true)  -> (true, snd w)
                                | (true,false) -> let h = concat (fst w) word
                                                  let t = collector state h
                                                  (wordExists state (concat (fst w) word), snd t)
                           else (false,0)  

        | (false,_)    -> (false, 0)
       
                            

    let check1XInc = check1 collectWordXInc incrementX appender
    let check1XDec = check1 collectWordXDec decrementX prepender
    let check1YInc = check1 collectWordYInc incrementY appender
    let check1YDec = check1 collectWordYDec decrementY prepender
    

    let checker checkAdj checkS state coord word word2 = 
        match checkAdj state coord word with
        | (true, p1)  -> match checkS state coord word2 with
                         | (true, p2) -> (true, p1 + p2)
                         | (false, _) -> (false, 0)
        
        | (false, _) -> (false, 0)

    
    let checkXInc = checker checkVertical check1XInc
    let checkXDec = checker checkVertical check1XDec
    let checkYInc = checker checkHorizontal check1YInc
    let checkYDec = checker checkHorizontal check1YDec


    // Match checkHorizontal with -> include points
    // Check horizontal on vertical and vice verce - Start from -/+1 and collect words
    // Look ahead does not work
    // Use dictionary step - search does not stop when word does not exist
    let findValidWords coordAdjuster checker concat concat2 (st : State) coord startingPoint =
        let rec go hand word existing c words =
            hand |> List.fold (fun x k -> let charr = Map.find k st.tiles
                                          let newWord = concat word [(c, (k, charr))] 
                                          let newExisting = concat2 existing [(c,charr)] 
                                          match checker st c [(c,charr)] newExisting with
                                          | (false, _) -> words
                                          | (true, p)  ->                         
                                          if   wordExists st newExisting
                                          then Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) (Map.add ((calcPoint newWord) + p) newWord words)) x 
                                          else Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) words) x
                                          
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty


    let findValidWordsXInc = findValidWords incrementX checkXInc appender appender
    let findValidWordsXDec = findValidWords decrementX checkXDec prepender prepender
    let findValidWordsYInc = findValidWords incrementY checkYInc appender appender
    let findValidWordsYDec = findValidWords decrementY checkYDec prepender prepender

  (*   let validWordExists st c start = List.map (fun x -> start@[c, (x, (Map.find x st.tiles))]) (MultiSet.toList st.hand) 
                                     |> List.filter (fun x -> wordExists2 st x)
                                     |> fun h -> if List.isEmpty h then None
                                                 else Some (h.[0].[1])

    |> fun x -> if squareExistsAndFree st (decrementY (fst first))
                                               then match validWordExists st (decrementY (fst first)) [fst first, (uint32 2, (snd first))] with
                                                    | Some m ->  Map.fold (fun acc key value -> 
                                                                 Map.add key value acc) x (findValidWordsXDec st (fst m) [] [m])
                                                                 |> fun t -> Some (Map.fold (fun acc key value -> 
                                                                                   Map.add key value acc) t (findValidWordsXInc st (fst m) [] [m])) 
                                                    | None   -> Some (x)
                                               
                                               else Some (x)   *)                         

    // Include point from all words -> include points from squares 
    // Place words horizontal on top of horizontal
    // Try with first char in middle of word
    let tryHorizontal (st : State) (first : coord*(char*int)) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> findValidWordsXInc st (incrementX (fst first)) ([first], 0)
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsXDec st (decrementX (fst first)) ([first],0)))
                            
       | ((_,true), (_,_))      -> let existing = collectWordXInc st [first]
                                   Some (findValidWordsXDec st (decrementX (fst first)) (existing))
                                   
      
       | ((_,_), (_,true))      -> let existing = collectWordXDec st [first]
                                   Some (findValidWordsXInc st (incrementX (fst first)) existing)

                            
    let tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> findValidWordsYInc st (incrementY (fst first)) ([first], 0)
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsYDec st (decrementY (fst first)) ([first],0)))
               
       | ((_,true), (_,_))    -> let existing = collectWordYInc st [first]
                                 Some (findValidWordsYDec st (decrementYTimes (fst first) (fst existing).Length) existing)

       | ((_,_), (_,true))    -> Some (findValidWordsYInc st (incrementY (fst first)) (collectWordYDec st [first]))

    let collectWords state =
        state.played |> Map.toList |> List.map (fun char -> tryHorizontal state char) 
                  |> fun x -> (List.map (fun char -> tryVertical state char) (Map.toList state.played)) @ x

    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
    let validSquares state word = List.forall (fun x -> match Map.tryFind (fst x) state.played with
                                                        | Some _ -> false
                                                        | None   -> true 
                                               ) word
                                    
    let extractResult state words =
        words |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
              |> Map.toList |> List.filter (fun (_, x) -> validMove state x) 
              |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))

    // Add prefix and postfix
    // Length x width
    // Write horizontal after checking vertical
    // Wildcard? 
    let findMove state = 
        if state.placeCenter then findValidWordsXInc state (0, 0) ([],0) 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
