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
 

    let checkSameDirection collector coordAdjuster concat concat2 state coord char existing word hand currentTile =
        let w : List<coord * (char * int)> * int = collector state [] coord
        match squareExistsAndFree2 state coord with
        | (true,false) -> (true, (coordAdjuster ((fst w).Length-1) coord), hand, (concat existing (fst w)), word)
                           
        | (true,true)  -> (true, coord, (removeFirst (fun m -> m = currentTile) hand), concat existing [coord, char], concat2 word [(coord, (currentTile, char))]) 
        | (false,_)    -> (false, coord, hand, (concat existing (fst w)), concat2 word [(coord, (currentTile, char))])


    let check1XInc = checkSameDirection collectWordXInc2 incrementXTimes appender appender
    let check1XDec = checkSameDirection collectWordXDec2 decrementXTimes prepender prepender
    let check1YInc = checkSameDirection collectWordYInc2 incrementYTimes appender appender
    let check1YDec = checkSameDirection collectWordYDec2 decrementYTimes prepender prepender
                                  
    let checker checkAdj checkS state coord char existing word hand currentTile =  
        match checkAdj state coord [coord, char] with
        | (true, p1)  -> match checkS state coord char existing word hand currentTile with
                         | (true,c,h,w,w1)  -> (true, p1, c, h, w, w1)
                         | (false,c,h,w,w1) -> (false, 0, c, h, w, w1)
        
        | (false, _) -> (false, 0, (0,0), [], [], [])

    let checkXInc = checker checkVertical check1XInc
    let checkXDec = checker checkVertical check1XDec
    let checkYInc = checker checkHorizontal check1YInc
    let checkYDec = checker checkHorizontal check1YDec

    // Use dictionary.step to prevent going on for to long
    let findValidWords coordAdjuster checker (st : State) coord startingPoint =
        let rec go hand word existing c words =
            hand |> List.fold (fun acc ele -> 
                    match checker st c (Map.find ele st.tiles) existing word hand ele with
                    | (false,_,_,_,_,_)       -> acc
                    | (true, p, c2, h, w, w1) -> match squareExistsAndFree2 st (coordAdjuster c) with
                                                 | (true,false) -> foldHelper3 (go h w1 w (coordAdjuster c2) words) acc
                                                 | (_,_)        -> if wordExists st w
                                                                   then foldHelper3 (go h w1 w (coordAdjuster c2) (Map.add ((calcPoints st w) + p) w1 words)) acc 
                                                                   else foldHelper3 (go h w1 w (coordAdjuster c2) words) acc 
                             ) words

        go (MultiSet.toList st.hand) [] (fst startingPoint) coord Map.empty

    let findValidWordsXInc = findValidWords incrementX checkXInc 
    let findValidWordsXDec = findValidWords decrementX checkXDec 
    let findValidWordsYInc = findValidWords incrementY checkYInc 
    let findValidWordsYDec = findValidWords decrementY checkYDec

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


    let collectWords1 state =
        state.played |> Map.toList |> fun x -> let tasks = [async {return List.map (fun char -> tryHorizontal state char) x}; async {return List.map (fun char -> tryVertical state char) x}]
                                               Async.RunSynchronously(Async.Parallel tasks)
                  

    let validMove state word = List.forall (fun x -> x <> word) state.failedPlays
    
    let validSquares state word = List.forall (fun x -> match Map.tryFind (fst x) state.played with
                                                        | Some _ -> false
                                                        | None   -> true 
                                               ) word
    // Only change when playing alone else pass  
    // Try with char in middle
    // Rename functions                      
    let extractResult state words =
        words |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
              |> Map.toList |> List.filter (fun (_, x) -> validMove state x)
              |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))


    let findMove state = 
        if state.placeCenter then findValidWordsXDec state (0, 0) ([],0) 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else SMPlay (snd (Seq.maxBy fst x))
        else collectWords state |> removeEmpty |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList state.hand) else extractResult state x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
