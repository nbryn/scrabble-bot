namespace nbryn
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open BoardUtil
open Types
open Utility
module internal MoveGenerator =

    let collectWord coordAdjuster concat adjustC (st : State) (word : List<coord*(char*int)>) coord   =
        let rec go word c p =
            if   not (squareFree st c)
            then go (concat word ([c, (Map.find c st.played)])) (coordAdjuster c) (p + (snd (Map.find c st.played)))              
            else (word,p)

        go word (if adjustC then coordAdjuster coord else coord) 0

    let collectWordXInc = collectWord incrementX appender true
    let collectWordXDec = collectWord decrementX prepender true
    let collectWordYInc = collectWord incrementY appender true
    let collectWordYDec = collectWord decrementY prepender true

    let collectWordXInc2 = collectWord incrementX appender false
    let collectWordXDec2 = collectWord decrementX prepender false
    let collectWordYInc2 = collectWord incrementY appender false
    let collectWordYDec2 = collectWord decrementY prepender false

    let checkWord collector state word coord =
        let word = collector state word coord
        ((wordExists state (fst word)), snd word)

    let checkWordXInc = checkWord collectWordXInc
    let checkWordXDec = checkWord collectWordXDec
    let checkWordYInc = checkWord collectWordYInc
    let checkWordYDec = checkWord collectWordYDec

    let checkVertical (st : State) coord word =
       match squareExistsAndFree2 st coord with
       | (true,false) -> (true, 0) 
       | _            ->
       match verticalChecker st coord with
       | ((true,false),(true,false)) -> let first = collectWordYDec st word (fst word.[0])
                                        let second = collectWordYInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((_,_),(true,false))        -> checkWordYInc st word (fst word.[0])    
       | ((true,false),(_,_))        -> checkWordYDec st word (fst word.[0])
       | ((_,_),(_,_))               -> (true, 0)

       
    let checkHorizontal (st : State) coord word=
       match squareExistsAndFree2 st coord with
       | (true,false) -> (true, 0) 
       | _            ->
       match horizontalChecker st coord with   
       | ((true,false),(true,false)) -> let first = collectWordXDec st word (fst word.[0])
                                        let second = collectWordXInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((_,_),(true,false))        -> checkWordXInc st word (fst word.[0])
       | ((true,false),(_,_))        -> checkWordXDec st word (fst word.[0])
       | ((_,_),(_,_))               -> (true, 0)
 
    
    let checkSameDirection collector coordAdjuster concat concat2 (state : State) coord char existing word hand currentTile =
        let w : List<coord*(char * int)> * int = collector state [] coord
        let newW = concat (concat existing (fst w)) [(coord, char)] 
        match squareExistsAndFree2 state coord with
        | (true,false) -> match stepDict newW state.dict with
                          | (true, inDict, _) -> (true, inDict, (coordAdjuster ((fst w).Length-1) coord), hand, newW, word, simpleCalcPoint (fst w))
                          | (false,_, _)      -> (false, false, coord, hand, newW, concat2 word [(coord, (currentTile, char))], 0)
                          
        | (true,true)  -> match stepDict newW state.dict with
                          | (true, inDict, _) -> (true, inDict, coord, (removeFirst (fun m -> m = currentTile) hand), newW, concat2 word [(coord, (currentTile, char))], 0)
                          | (false,_,_)       -> (false, false, coord, hand, [], concat2 word [], 0) 
                                                    
        | (false,_)    -> (false, false, coord, hand, [], concat2 word [(coord, (currentTile, char))], 0)


    let checkSameDirection2 collector coordAdjuster concat2 state coord char word hand currentTile dict =
        match squareExistsAndFree2 state coord with
        | (true,false) -> let w : List<coord * (char * int)> * int = collector state [] coord
                          match stepDict (fst w) dict with
                          | (true, inDict, d) -> (true, inDict, (coordAdjuster ((fst w).Length-1) coord), hand, d, word, simpleCalcPoint (fst w))
                          | (false,_, _)      -> (false, false, coord, hand, dict, concat2 word [], 0)
                             
        | (true,true)  -> match Dictionary.step (fst char) dict with
                          | Some (inDict, d) -> (true, inDict, coord, (removeFirst (fun m -> m = currentTile) hand), d, concat2 word [(coord, (currentTile, char))], 0) 
                          | None             -> (false, false, coord, hand, dict, concat2 word [], 0)
                          
        | (false,_)    -> (false, false, coord, hand, dict, concat2 word [], 0)
        

    let checkXSameInc = checkSameDirection2 collectWordXInc2 incrementXTimes appender
    let checkXSameDec = checkSameDirection collectWordXDec2 decrementXTimes prepender prepender
    let checkYSameDec = checkSameDirection collectWordYDec2 decrementYTimes prepender prepender
    let checkYSameInc = checkSameDirection2 collectWordYInc2 incrementYTimes appender
                                  
    let checkSorroundings checkAdj checkS state coord char word hand currentTile dict =  
        match checkAdj state coord [coord, char] with
        | (true, p1)  -> match checkS state coord char word hand currentTile dict with
                         | (true,inDict,c,h,d,w1, p2)  -> (true, inDict, p1 + p2, c, h, d, w1)
                         | (false,inDict,c,h,d,w1, p2) -> (false, inDict, p2, c, h, d, w1)
        
        | (false, _) -> (false, false, 0, (0,0), [], dict, [])

    let checkSorroundings2 checkAdj checkS state coord char word existing hand currentTile =  
        match checkAdj state coord [coord, char] with
        | (true, p1)  -> match checkS state coord char existing word hand currentTile with
                         | (true,inDict,c,h,nw,w1, p2)  -> (true, inDict, p1 + p2, c, h,nw, w1)
                         | (false,inDict,c,h,nw,w1, p2) -> (false, inDict, p2, c, h, nw, w1)
        
        | (false, _) -> (false, false, 0, (0,0), [], [], [])


    let checkXInc = checkSorroundings checkVertical checkXSameInc
    let checkXDec = checkSorroundings2 checkVertical checkXSameDec
    let checkYDec = checkSorroundings2 checkHorizontal checkYSameDec
    let checkYInc = checkSorroundings checkHorizontal checkYSameInc

    let findValidWords coordAdjuster checker (st : State) coord startingPoint =
        let rec go hand word existing c words =
            hand |> List.fold (fun acc ele -> 
                    match checker st c (Map.find ele st.tiles) word existing hand ele with
                    | (false,_,_,_,_,_,_)              -> acc
                    | (true, inDict, p, c2, h, nw, w1) -> 
                    match squareExistsAndFree2 st (coordAdjuster c) with
                    | (true,false) -> foldHelper3 (go h w1 nw (coordAdjuster c2) words) acc
                    | (_,_)        -> if inDict then foldHelper3 (go h w1 nw (coordAdjuster c2) (Map.add ((calcPoints st w1) + p) w1 words)) acc 
                                      else foldHelper3 (go h w1 nw (coordAdjuster c2) words) acc  
                                                                           
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty

    let findValidWords2 coordAdjuster checker (st : State) coord dict =
        let rec go hand word c words dict' =
            hand |> List.fold (fun acc ele -> 
                    match checker st c (Map.find ele st.tiles) word hand ele dict' with
                    | (false,_,_,_,_,_,_)             -> acc
                    | (true, inDict, p, c2, h, d, w1) -> 
                    match squareExistsAndFree2 st (coordAdjuster c) with
                    | (true,false) -> foldHelper3 (go h w1 (coordAdjuster c2) words d) acc 
                    | (_,_)        -> if inDict then foldHelper3 (go h w1 (coordAdjuster c2) (Map.add ((calcPoints st w1) + p) w1 words) d) acc
                                      else foldHelper3 (go h w1 (coordAdjuster c2) words d) acc 
                                                                           
                             ) words

        go (MultiSet.toList st.hand) [] coord Map.empty dict


    let findValidWordsXInc = findValidWords2 incrementX checkXInc 
    let findValidWordsXDec = findValidWords decrementX checkXDec
    let findValidWordsYDec = findValidWords decrementY checkYDec
    let findValidWordsYInc = findValidWords2 incrementY checkYInc 

    let applyH = apply findValidWordsYDec findValidWordsYInc collectWordYInc collectWordYDec findValidWordsXDec findValidWordsXInc
    let applyV = apply findValidWordsXDec findValidWordsXInc collectWordXInc collectWordXDec findValidWordsYDec findValidWordsYInc

    let tryHorizontal state first =
       match horizontalChecker state (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> apply2 findValidWordsYDec findValidWordsYInc collectWordYInc collectWordYDec findValidWordsXDec findValidWordsXInc decrementX incrementX state first
       
       | ((_,true), (_,_))      -> applyH decrementX incrementXTimes collectWordXInc state first true                                                                       
       | ((_,_), (_,true))      -> applyH incrementX decrementXTimes collectWordXDec state first true

    let tryVertical state first =
       match verticalChecker state (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> apply2 findValidWordsXDec findValidWordsXInc collectWordXInc collectWordXDec findValidWordsYDec findValidWordsYInc decrementY incrementY state first
                                    
       | ((_,true), (_,_))      -> applyV decrementY incrementYTimes collectWordYInc state first true
       | ((_,_), (_,true))      -> applyV incrementY decrementYTimes collectWordYDec state first false
      

    let collectWords state =
        state.played |> Map.toList |> List.map (fun char -> tryHorizontal state char) 
                  |> fun x -> (List.map (fun char -> tryVertical state char) (Map.toList state.played)) @ x

                              
    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
       
    let extractResult state words =
        words |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
              |> Map.toList |> List.filter (fun (_, x) -> validMove state x)
              |> fun x -> if List.isEmpty x then SMPass else SMPlay (snd (Seq.maxBy fst x))


    let findMove state = 
        if state.placeCenter then findValidWordsXInc state (0, 0) state.dict 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMPass else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMPass else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
