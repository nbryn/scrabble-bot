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

    let checkVertical (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match squareExistsAndFree2 st c with
       | (true,false) -> (true, 0) 
       | _            ->
       match verticalChecker st c with
       | ((true,false),(true,false)) -> let first = collectWordYDec st word (fst word.[0])
                                        let second = collectWordYInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((_,_),(true,false))        -> checkWordYInc st word (fst word.[0])    
       | ((true,false),(_,_))        -> checkWordYDec st word (fst word.[0])
       | ((_,_),(_,_))               -> (true, 0)

       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match squareExistsAndFree2 st c with
       | (true,false) -> (true, 0) 
       | _            ->
       match horizontalChecker st c with   
       | ((true,false),(true,false)) -> let first = collectWordXDec st word (fst word.[0])
                                        let second = collectWordXInc st word (fst word.[0])
                                        (wordExists st ((fst first).[0..(fst first).Length-2] @ (fst second)), (snd first) + (snd second))
       
       | ((_,_),(true,false))        -> checkWordXInc st word (fst word.[0])
       | ((true,false),(_,_))        -> checkWordXDec st word (fst word.[0])
       | ((_,_),(_,_))               -> (true, 0)
 

    let rec stepDictUnknown (word : List<coord*(char*int)>) (dict : Dictionary.Dict) = 
            if word.Length = 0 then (true, true, dict)
            else
            if word.Length = 1 then 
                               match Dictionary.step (fst (snd word.[0])) dict with
                               | Some (true, d)  -> (true, true, d)
                               | Some (false, d) -> (true, false, d)
                               | None            -> (false, false,  dict)
            else
            match Dictionary.step (fst (snd word.[0])) dict with
            | Some (_, d)  -> stepDictUnknown (word.[1..word.Length-1]) d
            | None         -> (false, false, dict)


    let simpleCalcPoint (word : List<coord * (char * int)>) = List.fold (fun acc ele -> (snd (snd ele)) + acc) 0 word

    
    let checkSameDirection collector coordAdjuster concat concat2 (state : State) coord char existing word hand currentTile =
        let w : List<coord*(char * int)> * int = collector state [] coord
        let s = concat existing (fst w)
        let newW = concat s [(coord, char)] 
        match stepDictUnknown newW state.dict with
        | (false,_, _) -> (false, false, coord, hand, newW, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w))
        | (true, inDict, d) -> 
        match squareExistsAndFree2 state coord with
        | (true,false) -> (true, inDict, (coordAdjuster ((fst w).Length-1) coord), hand, newW, word, simpleCalcPoint (fst w))
                           
        | (true,true)  -> (true, inDict, coord, (removeFirst (fun m -> m = currentTile) hand), newW, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w)) 
        | (false,_)    -> (false, inDict, coord, hand, newW, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w))
 
    
    let checkSameDirection2 collector coordAdjuster concat2 state coord char word hand currentTile dict =
        let w : List<coord * (char * int)> * int = collector state [] coord
        match stepDictUnknown (fst w) dict with
        | (false,_, _) -> (false, false, coord, hand, dict, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w))
        | (true, _, d)  ->
        match Dictionary.step (fst char) d with
        | None             -> (false, false, coord, hand, dict, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w))
        | Some (inDict, d) ->
        match squareExistsAndFree2 state coord with
        | (true,false) -> (true, inDict, (coordAdjuster ((fst w).Length-1) coord), hand, d, word, simpleCalcPoint (fst w))
                           
        | (true,true)  -> (true, inDict, coord, (removeFirst (fun m -> m = currentTile) hand), d, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w)) 
        | (false,_)    -> (false, inDict, coord, hand, d, concat2 word [(coord, (currentTile, char))], simpleCalcPoint (fst w))

 

    let check1XInc = checkSameDirection collectWordXInc2 incrementXTimes appender appender
    let check1XDec = checkSameDirection collectWordXDec2 decrementXTimes prepender prepender
    let check1YInc = checkSameDirection collectWordYInc2 incrementYTimes appender appender
    let check1YDec = checkSameDirection collectWordYDec2 decrementYTimes prepender prepender

    let check1XInc2 = checkSameDirection2 collectWordXInc2 incrementXTimes appender
    let check1XDec2 = checkSameDirection2 collectWordXDec2 decrementXTimes prepender
    let check1YInc2 = checkSameDirection2 collectWordYInc2 incrementYTimes appender
    let check1YDec2 = checkSameDirection2 collectWordYDec2 decrementYTimes prepender
                                  
    let checker2 checkAdj checkS state coord char word hand currentTile (dict : Dictionary.Dict) =  
        match checkAdj state coord [coord, char] with
        | (true, p1)  -> match checkS state coord char word hand currentTile dict with
                         | (true,inDict,c,h,d,w1, p2)  -> (true, inDict, p1 + p2, c, h, d, w1)
                         | (false,inDict,c,h,d,w1, p2) -> (false, inDict, p2, c, h, d, w1)
        
        | (false, _) -> (false, false, 0, (0,0), [], dict, [])

    let checker3 checkAdj checkS state (coord : coord) char (word : List<coord *(uint32* (char * int))>) existing hand currentTile =  
        match checkAdj state coord [coord, char] with
        | (true, p1)  -> match checkS state coord char existing word hand currentTile with
                         | (true,inDict,c,h,nw,w1, p2)  -> (true, inDict, p1 + p2, c, h,nw, w1)
                         | (false,inDict,c,h,nw,w1, p2) -> (false, inDict, p2, c, h, nw, w1)
        
        | (false, _) -> (false, false, 0, (0,0), [], [], [])

    let checkXInc = checker3 checkVertical check1XInc
    let checkXDec = checker3 checkVertical check1XDec
    let checkYInc = checker3 checkHorizontal check1YInc
    let checkYDec = checker3 checkHorizontal check1YDec

    let checkXInc2 = checker2 checkVertical check1XInc2
    let checkXDec2 = checker2 checkVertical check1XDec2
    let checkYInc2 = checker2 checkHorizontal check1YInc2
    let checkYDec2 = checker2 checkHorizontal check1YDec2

    let findValidWords2 coordAdjuster checker (st : State) coord dict =
        let rec go hand word c words dict' =
            hand |> List.fold (fun acc ele -> 
                    match checker st c (Map.find ele st.tiles) word hand ele dict' with
                    | (false,_,_,_,_,_,_)             -> acc
                    | (true, inDict, p, c2, h, d, w1) -> 
                    match squareExistsAndFree2 st (coordAdjuster c) with
                    | (true,false) -> foldHelper3 (go h w1 (coordAdjuster c2) words d) acc 
                    | (_,_)        -> if inDict then foldHelper3 (go h w1 (coordAdjuster c2) (Map.add ((calcPoints2 st w1) + p) w1 words) d) acc
                                      else foldHelper3 (go h w1 (coordAdjuster c2) words d) acc 
                                                                           
                             ) words

        go (MultiSet.toList st.hand) [] coord Map.empty dict


    let findValidWords3 coordAdjuster checker (st : State) coord startingPoint =
        let rec go hand word existing c words =
            hand |> List.fold (fun acc ele -> 
                    match checker st c (Map.find ele st.tiles) word existing hand ele with
                    | (false,_,_,_,_,_,_)              -> acc
                    | (true, inDict, p, c2, h, nw, w1) -> 
                    match squareExistsAndFree2 st (coordAdjuster c) with
                    | (true,false) -> foldHelper3 (go h w1 nw (coordAdjuster c2) words) acc
                    | (_,_)        -> if inDict then foldHelper3 (go h w1 nw (coordAdjuster c2) (Map.add ((calcPoints2 st w1) + p) w1 words)) acc 
                                      else foldHelper3 (go h w1 nw (coordAdjuster c2) words) acc  
                                                                           
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty

    let findValidWordsXInc = findValidWords3 incrementX checkXInc 
    let findValidWordsXDec = findValidWords3 decrementX checkXDec
    let findValidWordsYInc = findValidWords3 incrementY checkYInc 
    let findValidWordsYDec = findValidWords3 decrementY checkYDec

    let findValidWordsXInc2 = findValidWords2 incrementX checkXInc2 
    let findValidWordsXDec2 = findValidWords2 decrementX checkXDec2 
    let findValidWordsYInc2 = findValidWords2 incrementY checkYInc2 
    let findValidWordsYDec2 = findValidWords2 decrementY checkYDec2

    let foldHelper6 f1 f2 collector collector2 (state : State) coord =
        let (_,_,newD) = stepDictUnknown (fst (collector2 state [] coord)) state.dict
        Map.fold (fun acc key value ->
        Map.add key value acc) (f1 state coord (collector state [] coord)) (f2 state coord newD)

    let foldHelper f1 f2 firstAdjuster secondAdjuster (state : State) char =
        let s = snd (Dictionary.step (fst (snd char)) state.dict).Value
        Map.fold (fun acc key value ->
        Map.add key value acc) (f1 state (firstAdjuster (fst char)) ([char], 0)) (f2 state (secondAdjuster (fst char)) s)

    
    let apply5 stF stF2 collector2 collector3 firstF secondF fAdjuster sAdjuster collector1 (state : State) char xt  =
        let existing : List<coord * (char * int)> * int = collector1 state [char] (fst char)
        let (_,_,newD) = stepDictUnknown (fst existing) state.dict
        foldHelper6 stF stF2 collector2 collector3 state (fAdjuster (fst char))
        |> fun fm -> firstF state (if xt then fAdjuster (fst char) else sAdjuster (fst existing).Length (fst char)) existing |> foldHelper3 fm
        |> fun sm -> Some (foldHelper3 sm (secondF state (if xt then sAdjuster (fst existing).Length (fst char) else fAdjuster (fst char)) newD))

    let apply2 stF stF2 collector1 collector2 firstF secondF firstAdjuster secondAdjuster state char =
        foldHelper6 stF stF2 collector1 collector2 state (firstAdjuster (fst char))
        |> foldHelper3 (foldHelper6 stF stF2 collector1 collector2 state (secondAdjuster (fst char)))
        |> fun thirdM -> Some (foldHelper3 thirdM (foldHelper firstF secondF firstAdjuster secondAdjuster state char))

    
    let applyH2 = apply5 findValidWordsYDec findValidWordsYInc2 collectWordYInc collectWordYDec findValidWordsXDec findValidWordsXInc2
    let applyV2 = apply5 findValidWordsXDec findValidWordsXInc2 collectWordXInc collectWordXDec findValidWordsYDec findValidWordsYInc2

    let rec tryHorizontal (st : State) (first : coord*(char*int)) =
       match horizontalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None
       | ((_,true), (_,true))   -> apply2 findValidWordsYDec findValidWordsYInc2 collectWordYInc collectWordYDec findValidWordsXDec findValidWordsXInc2 incrementX decrementX st first
       
       | ((_,true), (_,_))      -> applyH2 decrementX incrementXTimes collectWordXInc st first true                                                                       
       | ((_,_), (_,true))      -> applyH2 incrementX decrementXTimes collectWordXDec st first true

    and tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> apply2 findValidWordsXDec findValidWordsXInc2 collectWordXInc collectWordXDec findValidWordsYDec findValidWordsYInc2 incrementY decrementY st first
                                    
       | ((_,true), (_,_))      -> applyV2 decrementY incrementYTimes collectWordYInc st first true
       | ((_,_), (_,true))      -> applyV2 incrementY decrementYTimes collectWordYDec st first false
      

    let collectWords state =
        state.played |> Map.toList |> List.map (fun char -> tryHorizontal state char) 
                  |> fun x -> (List.map (fun char -> tryVertical state char) (Map.toList state.played)) @ x

                              
    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
    
    
    let extractResult state words =
        words |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
              |> Map.toList |> List.filter (fun (_, x) -> validMove state x)
              |> fun x -> if List.isEmpty x then SMPass else SMPlay (snd (Seq.maxBy fst x))


    let findMove state = 
        if state.placeCenter then findValidWordsXInc state (0, 0) ([],0) 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMPass else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMPass else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
