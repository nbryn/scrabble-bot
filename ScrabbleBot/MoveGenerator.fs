namespace nbryn
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open BoardUtil
open Types
open Utility
module internal MoveGenerator =

    let collectWord coordAdjuster concat (st : State) (word : List<coord*(char*int)>)  =
        let rec go word c =
            if   squareExistsAndNotFree st c
            then go (concat word (c, (Map.find c st.played))) (coordAdjuster c)                
            else word

        go word (coordAdjuster (fst word.[0]))

    let collectWordXInc = collectWord incrementX appender
    let collectWordXDec = collectWord decrementX prepender
    let collectWordYInc = collectWord incrementY appender
    let collectWordYDec = collectWord decrementY prepender

    // Return tuple (bool*points)
    let checkVertical (st : State) (c : coord) (word : List<coord*(char*int)>) =
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
       
    let checkHorizontal (st : State) (c : coord) (word : List<coord*(char*int)>) =
       match horizontalChecker st c with
       | ((_,true),(_,true))         -> true
       | ((false,_),(_,_))           -> false 
       | ((_,true),(false,_))        -> true 
       | ((_,true),(true,false))     -> wordExists st (collectWordXInc st word)
       | ((true,false),(true,false)) -> let first = collectWordXInc st word
                                        wordExists st (first.[0..first.Length-2] @ collectWordXDec st word)
       | ((true,false),(false,_))    -> wordExists st (collectWordXDec st word)
       | ((true,false),(_,_))        -> wordExists st (collectWordXDec st word)
 
    let calcPoint (l : List<coord*(uint32*(char*int))>) = List.fold (fun acc (_, (_, (_,x))) -> acc + x) 0 l

    // Use special checker for  
    let check1 collector coordAdjuster state coord word =
        match squareExistsAndFree2 state (coordAdjuster coord) with
        | (_,true)      -> true
        | (false,_)     -> false
        | (true,false)  -> wordExists state (collector state word)

    let check1XDec = check1 collectWordXDec decrementX
    let check1XInc = check1 collectWordXInc incrementX
    let check1YDec = check1 collectWordYDec decrementY
    let check1YInc = check1 collectWordYInc incrementY

    // Match checkHorizontal with -> include points
    // Check horizontal on vertical and vice verce - Start from -/+1 and collect words
    // Look ahead does not work
    // Merge all checkers in one function?
    let findValidWords coordAdjuster checker check1 concat concat2 (st : State) coord startingPoint =
        let rec go hand word existing c words =
            hand |> List.fold (fun x k -> let charr = Map.find k st.tiles
                                          let newWord = concat word (c, (k, charr)) 
                                          let newExisting = concat2 existing (c,charr) 
                                          if (not (checker st c [(c,charr)]) || not (check1 st c newExisting))
                                          then words
                                          else                           
                                          if   wordExists st newExisting
                                          then Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) (Map.add (calcPoint newWord) newWord words)) x 
                                          else Map.fold (fun acc key value -> 
                                               Map.add key value acc) (go (removeFirst (fun m -> m = k ) hand) newWord newExisting (coordAdjuster c) words) x
                                          
                             ) words

        go (MultiSet.toList st.hand) [] startingPoint coord Map.empty


    let findValidWordsXInc = findValidWords incrementX checkVertical check1XInc appender appender
    let findValidWordsXDec = findValidWords decrementX checkVertical check1XDec prepender prepender
    let findValidWordsYInc = findValidWords incrementY checkHorizontal check1YInc appender appender
    let findValidWordsYDec = findValidWords decrementY checkHorizontal check1YDec prepender prepender

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
       | ((_,true), (_,true))   -> findValidWordsXInc st (incrementX (fst first)) [first]
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsXDec st (decrementX (fst first)) [first]))
                            
       | ((_,true), (_,_))      -> Some (findValidWordsXDec st (decrementX (fst first)) (collectWordXInc st [first]))
                                   
      
       | ((_,_), (_,true))      -> Some (findValidWordsXDec st (decrementXTimes (fst first) (collectWordXDec st [first]).Length) (collectWordXDec st [first]))

                            
    let tryVertical (st : State) (first : coord*(char*int)) =
       match verticalChecker st (fst first) with
       | ((false,_), (false,_)) -> None
       | ((_,false), (_,false)) -> None                           
       | ((_,true), (_,true))   -> findValidWordsYInc st (incrementY (fst first)) [first]
                                   |> fun x -> Some (Map.fold (fun acc key value -> 
                                                     Map.add key value acc) x (findValidWordsYDec st (decrementY (fst first)) [first]))
               
       | ((_,true), (_,_))    -> let existingWord = collectWordYInc st [first]          
                                 Some (findValidWordsYDec st (decrementYTimes (fst first) existingWord.Length) existingWord)

       | ((_,_), (_,true))    -> Some (findValidWordsYInc st (incrementY (fst first)) (collectWordYDec st [first]))

    let collectWords (st : State) =
        st.played |> Map.toList |> List.map (fun char -> tryHorizontal st char) 
                  |> fun x -> (List.map (fun char -> tryVertical st char) (Map.toList st.played)) @ x

    let validMove (st : State) word = List.forall (fun x -> x <> word) st.failedPlays
                                    
    let extractResult (st : State) (l : list<Map<int,list<coord*(uint32*(char * int))>>>) =
        l |> List.fold (fun acc value -> Map.fold (fun a k v -> Map.add k v a) acc value) Map.empty
          |> Map.toList |> List.filter (fun (_, x) -> validMove st x) 
          |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList st.hand) else SMPlay (snd (Seq.maxBy fst x))

    // Add prefix and postfix
    // Length x width
    // Write horizontal after checking vertical
    // Wildcard? 
    let findMove (st : State) = 
        if st.placeCenter then findValidWordsXInc st (0, 0) [] 
                               |> Map.toList 
                               |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList st.hand) else SMPlay (snd (Seq.maxBy fst x))
        else collectWords st |> removeEmpty |> fun x -> if List.isEmpty x then SMChange (MultiSet.toList st.hand) else extractResult st x
                      
    let convertState b d h p t pc fp = {board = b; dict = d; hand = h; played = p; tiles = t; placeCenter = pc; failedPlays = fp;}
