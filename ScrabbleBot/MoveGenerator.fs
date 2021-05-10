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
    // Fewer cases
    let checkVertical (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match verticalChecker st c with
       | ((false,_),(true,false))    -> checkWordYInc st word
       | ((_,true),(true,false))     -> checkWordYInc st word
       
       | ((true,false),(true,false)) -> let first = collectWordYDec st word
                                        let second = collectWordYInc st word
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((true,false),(false,_))    -> checkWordYDec st word
       | ((true,false),(_,_))        -> checkWordYDec st word
       | (_,(true,_))                -> (true, 0)
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(false,_))       -> (false, 0)  
       | ((_,true),(false,_))        -> (true, 0)
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match horizontalChecker st c with   
       | ((_,true),(true,false))     -> checkWordXInc st word
       | ((true,false),(_,true))     -> checkWordXDec st word
       | ((true,false),(true,false)) -> let first = collectWordXDec st word
                                        let second = collectWordXInc st word
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))

       | ((true,false),(false,_))    -> checkWordXDec st word
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(_,_))           -> (false, 0) 
       | ((_,true),(false,_))        -> (true, 0) 
                                        
    // Move to util
    let calcPoint (l : List<coord*(char*int)>) = List.fold (fun acc (_,(_,x)) -> acc + x) 0 l

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
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) (Map.add ((calcPoint newExisting) + p) newWord words)) acc 
                                               else Map.fold (fun acc key value -> 
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) words) acc
                                          
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty


    let findValidWordsXInc = findValidWords incrementX checkXInc appender appender
    let findValidWordsXDec = findValidWords decrementX checkXDec prepender prepender
    let findValidWordsYInc = findValidWords incrementY checkYInc appender appender
    let findValidWordsYDec = findValidWords decrementY checkYDec prepender prepender

    // Merge into one and move to util?
    let apply collector firstF secondF fAdjuster sAdjuster state char xt  =
        let (existing : List<coord * (char * int)> * int) = collector state [char]
        firstF state (if xt then fAdjuster (fst char) else sAdjuster (fst existing).Length (fst char)) existing
        |> fun x -> Some (Map.fold (fun acc key value ->
                          Map.add key value acc) x (secondF state (if xt then sAdjuster (fst existing).Length (fst char) else fAdjuster (fst char)) existing))

  
    let apply2 firstF secondF firstAdjuster secondAdjuster state char =
        firstF state (firstAdjuster (fst char)) ([char], 0)
        |> fun x -> Some (Map.fold (fun acc key value ->
                          Map.add key value acc) x (secondF state (secondAdjuster (fst char)) ([char], 0)))

    let apply3 collectOpposite collector firstF secondF fAdjuster sAdjuster state char xt =
        collectOpposite state char 
        |> fun t ->
        let (existing : List<coord * (char * int)> * int) = collector state [char]
        firstF state (if xt then fAdjuster (fst char) else sAdjuster (fst existing).Length (fst char)) existing
        |> fun x -> Map.fold (fun acc key value ->
                    Map.add key value acc) x (secondF state (if xt then sAdjuster (fst existing).Length (fst char) else fAdjuster (fst char)) existing)
        |> fun h -> h :: t            

    // Include point from all words -> include points from squares 
    // Try with first char in middle of word   
    // Wildcard? 
    // Place words vertical on top of horizontal & vice verca
    // TRY MULTIPLAYER
    // INCLUDE COLLECT IN APPLY
    // DONT INCLUDE FIRST IN COLLECT
    let tryHorizontal (st : State) (first : coord*(char*int)) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> apply2 findValidWordsXInc findValidWordsXDec incrementX decrementX st first
       
       | ((_,true), (_,_))      -> apply collectWordXInc findValidWordsXDec findValidWordsXInc decrementX incrementXTimes st first true              
                                                            
       | ((_,_), (_,true))      -> apply collectWordXDec findValidWordsXInc findValidWordsXDec incrementX decrementXTimes st first true


    // Problems with looking hortizontal on vertical inc
    let tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> apply2 findValidWordsYInc findValidWordsYDec incrementY decrementY st first
                                    
       | ((_,true), (_,_))      -> apply collectWordYInc findValidWordsYDec findValidWordsYInc decrementY incrementYTimes st first true
       | ((_,_), (_,true))      -> apply collectWordYDec findValidWordsYDec findValidWordsYInc incrementY decrementYTimes st first false
      

    let collectOpposite (oppositeF : State -> coord*(char*int) -> option<Map<int,list<(coord) * (uint32 * (char * int))>>>) cAdjuster concat index (st : State) (first : coord*(char*int)) : List<option<Map<int,list<(coord) * (uint32 * (char * int))>>>> =
       MultiSet.toList st.hand |> List.fold (fun acc ele -> 
                                            [concat [(cAdjuster (fst first), Map.find ele st.tiles)] [first]] @ acc) []
                               |> fun x -> if List.isEmpty x then List.empty
                                           else List.map (fun (x : list<coord * (char * int)>) -> oppositeF st (x.[index])) x                                  

       
    let collectOppositeXInc = collectOpposite tryVertical incrementX appender 1
    let collectOppositeXDec = collectOpposite tryVertical decrementX prepender 0  
    let collectOppositeYInc = collectOpposite tryHorizontal incrementY appender 1
    let collectOppositeYDec = collectOpposite tryHorizontal decrementY prepender 0


    let collectWords state =
        state.played |> Map.toList |> List.map (fun char -> tryHorizontal state char) 
                  |> fun x -> (List.map (fun char -> tryVertical state char) (Map.toList state.played)) @ x

    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
    
    // Look into if/why this is needed
    let validSquares state word = List.forall (fun x -> match Map.tryFind (fst x) state.played with
                                                        | Some _ -> false
                                                        | None   -> true 
                                               ) word
                                    
    let extractResult state words =
        words |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
              |> Map.toList |> List.filter (fun (_, x) -> validMove state x && validSquares state x) 
              |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))

    let findMove state = 
        if state.placeCenter then findValidWordsXInc state (0, 0) ([],0) 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
