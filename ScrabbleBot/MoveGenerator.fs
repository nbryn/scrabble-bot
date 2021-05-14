namespace nbryn
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open BoardUtil
open Types
open Utility
module internal MoveGenerator =

    let collectWord coordAdjuster concat (st : State) (word : List<coord*(char*int)>) coord  =
        let rec go word c p =
            if   not (squareFree st c)
            then go (concat word ([c, (Map.find c st.played)])) (coordAdjuster c) (p + (snd (Map.find c st.played)))              
            else (word,p)

        go word (coordAdjuster coord) 0

    let collectWordXInc = collectWord incrementX appender
    let collectWordXDec = collectWord decrementX prepender
    let collectWordYInc = collectWord incrementY appender
    let collectWordYDec = collectWord decrementY prepender

    let checkWord collector state word coord =
        let word = collector state word coord
        ((wordExists state (fst word)), snd word)

    let checkWordXInc = checkWord collectWordXInc
    let checkWordXDec = checkWord collectWordXDec
    let checkWordYInc = checkWord collectWordYInc
    let checkWordYDec = checkWord collectWordYDec

    let checkVertical (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match verticalChecker st c with
       | ((false,_),(true,false))    -> checkWordYInc st word (fst word.[0])
       | ((_,true),(true,false))     -> checkWordYInc st word (fst word.[0])
       
       | ((true,false),(true,false)) -> let first = collectWordYDec st word (fst word.[0])
                                        let second = collectWordYInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((true,false),(false,_))    -> checkWordYDec st word (fst word.[0])
       | ((true,false),(_,_))        -> checkWordYDec st word (fst word.[0])
       | (_,(true,_))                -> (true, 0)
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(false,_))       -> (false, 0)  
       | ((_,true),(false,_))        -> (true, 0)
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match horizontalChecker st c with   
       | ((_,true),(true,false))     -> checkWordXInc st word (fst word.[0])
       | ((true,false),(_,true))     -> checkWordXDec st word (fst word.[0])
       | ((true,false),(true,false)) -> let first = collectWordXDec st word (fst word.[0])
                                        let second = collectWordXInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))

       | ((true,false),(false,_))    -> checkWordXDec st word (fst word.[0])
       | ((_,true),(_,true))         -> (true, 0)
       | ((false,_),(_,_))           -> (false, 0) 
       | ((_,true),(false,_))        -> (true, 0) 

    // Pass existing as arg -> return newExisting from this? Then possible to continue after                            
    let checkSameDirection collector coordAdjuster concat state coord word =
        let w = collector state word coord  
        match squareExistsAndFree2 state coord with
        | (true,t)  -> match squareExistsAndFree2 state (coordAdjuster coord) with
                       | (false,_)    -> true
                       | (true,true)  -> true
                       | (true,false) -> if t then wordExists state (concat (fst w) word)                               // Error here?
                                              else wordExists state (concat (fst (collector state (concat (fst w) word) (fst (concat (fst w) word).[0]))) word)
        | (false,_) -> false

    let checkSameDirection1 collector coordAdjuster concat state coord word =
        let w = collector state word coord  
        match squareExistsAndFree2 state coord with
        | (true,false) -> (true, concat word w)
                           
        | (true,true)  -> (true, []) 
        | (false,_)    -> (false, [])
                                  
    let check1XInc = checkSameDirection collectWordXInc incrementX appender
    let check1XDec = checkSameDirection collectWordXDec decrementX prepender
    let check1YInc = checkSameDirection collectWordYInc incrementY appender
    let check1YDec = checkSameDirection collectWordYDec decrementY prepender
    
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

    // In checker after collecting word return word and increment coord -> try placing after
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
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) (Map.add ((calcPoints st newExisting) + p) newWord words)) acc 
                                               else Map.fold (fun acc key value -> 
                                                    Map.add key value acc) (go (removeFirst (fun m -> m = ele) hand) newWord newExisting (coordAdjuster c) words) acc
                                          
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty

    let findValidWordsXInc = findValidWords incrementX checkXInc appender appender
    let findValidWordsXDec = findValidWords decrementX checkXDec prepender prepender
    let findValidWordsYInc = findValidWords incrementY checkYInc appender appender
    let findValidWordsYDec = findValidWords decrementY checkYDec prepender prepender

    // Need to increment coord when calling first findValidWords in foldHelper2
    let apply stF stF2 collector2 collector3 firstF secondF fAdjuster sAdjuster collector1 state char xt  =
        let (existing : List<coord * (char * int)> * int) = collector1 state [char] (fst char)
        foldHelper2 stF stF2 collector2 collector3 state (fAdjuster (fst char))
        |> fun fm -> firstF state (if xt then fAdjuster (fst char) else sAdjuster (fst existing).Length (fst char)) existing |> foldHelper3 fm
        |> fun sm -> Some (foldHelper3 sm (secondF state (if xt then sAdjuster (fst existing).Length (fst char) else fAdjuster (fst char)) existing))
 

    let apply2 stF stF2 collector1 collector2 firstF secondF firstAdjuster secondAdjuster state char =
        foldHelper2 stF stF2 collector1 collector2 state (firstAdjuster (fst char))
        |> foldHelper3 (foldHelper2 stF stF2 collector1 collector2 state (secondAdjuster (fst char)))
        |> fun thirdM -> Some (foldHelper3 thirdM (foldHelper firstF secondF firstAdjuster secondAdjuster state char))

    
    let applyH = apply findValidWordsYDec findValidWordsYInc collectWordYInc collectWordYDec findValidWordsXDec findValidWordsXInc
    let applyV = apply findValidWordsXDec findValidWordsXInc collectWordXInc collectWordXDec findValidWordsYDec findValidWordsYInc

    let rec tryHorizontal (st : State) (first : coord*(char*int)) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> apply2 findValidWordsYDec findValidWordsYInc collectWordYInc collectWordYDec findValidWordsXInc findValidWordsXDec incrementX decrementX st first
       
       | ((_,true), (_,_))      -> applyH decrementX incrementXTimes collectWordXInc st first true                                                                        
       | ((_,_), (_,true))      -> applyH incrementX decrementXTimes collectWordXDec st first true

    and tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> apply2 findValidWordsXDec findValidWordsXInc collectWordXInc collectWordXDec findValidWordsYInc findValidWordsYDec incrementY decrementY st first
                                    
       | ((_,true), (_,_))      -> applyV decrementY incrementYTimes collectWordYInc st first true
       | ((_,_), (_,true))      -> applyV incrementY decrementYTimes collectWordYDec  st first false
      

    let collectWords state =
        state.played |> Map.toList |> List.map (fun char -> tryHorizontal state char) 
                  |> fun x -> (List.map (fun char -> tryVertical state char) (Map.toList state.played)) @ x

    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
    
    let validSquares state word = List.forall (fun x -> match Map.tryFind (fst x) state.played with
                                                        | Some _ -> false
                                                        | None   -> true 
                                               ) word

    // Check calc points is correct   
    // Only change when playing alone else pass  
    // Try with word in middle
    // Rename functions                      
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
