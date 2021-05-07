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
                                        
    // Move to util
    let calcPoint (l : List<coord*(uint32*(char*int))>) = List.fold (fun acc (_, (_, (_,x))) -> acc + x) 0 l

    let check1 collector coordAdjuster concat state coord word =
        let w = collector state word 
        match squareExistsAndFree2 state coord with
        | (true,t)  -> match squareExistsAndFree2 state (coordAdjuster coord) with
                       | (false,_)    -> true
                       | (true,true)  -> true
                       | (true,false) -> if t then wordExists state (concat (fst w) word)
                                              else wordExists state (concat (fst (collector state (concat (fst w) word))) word)
        | (false,_) -> false
       
                            
    let check1XInc = check1 collectWordXInc incrementX appender
    let check1XDec = check1 collectWordXDec decrementX prepender
    let check1YInc = check1 collectWordYInc incrementY appender
    let check1YDec = check1 collectWordYDec decrementY prepender
    

    let checker checkAdj checkS state coord word word2 = 
        match checkAdj state coord word with
        | (true, p1)  -> match checkS state coord word2 with
                         | true  -> (true, p1)
                         | false -> (false, 0)
        
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
            hand |> List.fold (fun acc ele -> 
                               let charr = Map.find ele st.tiles
                               let newWord = concat word [(c, (ele, charr))] 
                               let newExisting = concat2 existing [(c,charr)] 
                               match checker st c [(c,charr)] newExisting with
                               | (false, _) -> acc
                               | (true, p)  -> if wordExists st newExisting
                                               then Map.fold (fun acc key value -> 
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) (Map.add ((calcPoint newWord) + p) newWord words)) acc 
                                               else Map.fold (fun acc key value -> 
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) words) acc
                                          
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty


    let findValidWordsXInc = findValidWords incrementX checkXInc appender appender
    let findValidWordsXDec = findValidWords decrementX checkXDec prepender prepender
    let findValidWordsYInc = findValidWords incrementY checkYInc appender appender
    let findValidWordsYDec = findValidWords decrementY checkYDec prepender prepender

    // Merge into one and move to util?
    let apply firstF secondF firstAdjuster secondAdjuster state char (existing : List<coord * (char * int)> * int) =
        firstF state (firstAdjuster (fst char)) existing
        |> fun x -> Some (Map.fold (fun acc key value ->
                          Map.add key value acc) x (secondF state (secondAdjuster (fst char) (fst existing).Length) existing))


    let apply2 firstF secondF firstAdjuster secondAdjuster state char =
        firstF state (firstAdjuster (fst char)) ([char], 0)
        |> fun x -> Some (Map.fold (fun acc key value ->
                          Map.add key value acc) x (secondF state (secondAdjuster (fst char)) ([char], 0)))
                  
    // Include point from all words -> include points from squares 
    // Try with first char in middle of word   
    // Wildcard? 
    // Place words vertical on top of horizontal & vice verca
    // INCLUDE POINTS FROM EXISTING WORD
    // FIND ERRORS
    // TRY MULTIPLAYER
    let tryHorizontal (st : State) (first : coord*(char*int)) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> apply2 findValidWordsXInc findValidWordsXDec incrementX decrementX st first
       
       | ((_,true), (_,_))      -> let existing = collectWordXInc st [first]
                                   apply findValidWordsXDec findValidWordsXInc decrementX incrementXTimes st first existing                 
                                                            
       | ((_,_), (_,true))      -> let existing = collectWordXDec st [first]
                                   apply findValidWordsXInc findValidWordsXDec incrementX decrementXTimes st first existing
             
    let tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> apply2 findValidWordsYInc findValidWordsYDec incrementY decrementY st first
                                    
       | ((_,true), (_,_))      -> let existing = collectWordYInc st [first]
                                   apply findValidWordsYDec findValidWordsYInc decrementY incrementYTimes st first existing

       | ((_,_), (_,true))      -> let existing = collectWordYInc st [first]
                                   apply findValidWordsYDec findValidWordsYInc decrementY incrementYTimes st first existing

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

    let findMove state = 
        if state.placeCenter then findValidWordsXInc state (0, 0) ([],0) 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
