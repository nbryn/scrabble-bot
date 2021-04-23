namespace nbryn

open Parser
open ScrabbleUtil

module internal MoveGenerator =
  
    type State = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, (uint32*(char*int))>
        lastPlayed    : List<coord*(uint32*(char*int))>
        tiles         : Map<uint32, char*int>
    }

    type Surrounding = bool*bool

    let incrementX (c : coord) : coord = (fst c + 1, snd c)
    let decrementX (c : coord) : coord = (fst c - 1, snd c)
    let incrementY (c : coord) : coord  = (fst c, snd c + 1)
    let decrementY (c : coord) : coord  = (fst c, snd c - 1)
        
    let incrementCoord (c : coord) (incX : bool) : coord  = if incX then incrementX c else incrementY c
    let decrementCoord (c : coord) (decX : bool) : coord  = if decX then decrementX c else decrementY c

    let squareExist (st : State) (coord : coord) =
        match st.board.squares coord with
        | Some _ -> true
        | None   -> false

    let squareFree (st : State) (coord : coord) =
        match Map.tryFind coord st.played with
        | Some _ -> false
        | None   -> true

    let squareExistsAndFree (st : State) (coord : coord) =
        squareExist st coord && squareFree st coord

    let verticalChecker (st : State) (c : coord) : Surrounding = 
        (squareExist st (incrementY c), squareExist st (decrementY c))

    let horizontalChecker (st : State) (c : coord) : Surrounding = 
        (squareExist st (incrementX c), squareExist st (decrementX c))

    let rec removeFirst pred lst =
        match lst with
        | h::t when pred h -> t
        | h::t -> h::removeFirst pred t
        | _ -> []
        
    let wordExists (st : State) (list : List<coord*(uint32*(char*int))>) =
        let word = List.map (fun (m, (x, (y, z))) -> y) list |> List.toArray |> System.String
        ScrabbleUtil.Dictionary.lookup word st.dict

    let getVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go st c word =
            let newCoord = if increment then incrementY c else decrementY c
            if squareExist st newCoord
            then Map.find newCoord st.played 
                 |> fun x -> if increment then [(newCoord, (fst x, snd x))]@word else word@[(newCoord, (fst x, snd x))]
                 |> go st newCoord
            
            else word

        go st c word

    let getHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go st c word =    
            let newCoord = if increment then incrementX c else decrementX c
            if squareExist st newCoord
            then Map.find newCoord st.played 
                 |> fun x -> if increment then word@[(newCoord, (fst x, snd x))] else [(newCoord, (fst x, snd x))]@word
                 |> go st newCoord
            
            else word

        go st c word

    let checkVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match verticalChecker st c with
       | (false, false) -> false      
       | (true, false)  -> wordExists st (getVertical st c word true)
       | (false, true)  -> wordExists st (getVertical st c word false)
       | (true, true)   -> let first = getVertical st c word true
                           wordExists st (first.[0..first.Length-2] @ getVertical st c word false)

    let checkHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) =
       match horizontalChecker st c with
       | (false, false) -> false      
       | (true, false)  -> wordExists st (getHorizontal st c word true)
       | (false, true)  -> wordExists st (getHorizontal st c word false)
       | (true, true)   -> let first = getHorizontal st c word false
                           wordExists st (first.[0..first.Length-2] @ getHorizontal st c word true)
       
    // Need to find special squares (single etc)   
    let findBestWord (words : List<List<coord*(uint32*(char*int))>>) =
        //if List.isEmpty words then [(1*1, (3, 'c', 2))]
        words |> List.map (fun x -> List.fold (fun acc (_, (_, (_,z))) -> acc + z) 0 x)
        |> Seq.mapi (fun i v -> i, v) |> Seq.maxBy snd |> fun x -> words.[fst x]

    let createWordHorizontal (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go (hand : List<uint32>) (word : List<coord*(uint32*(char*int))>) (c : coord)  =
            if (squareExistsAndFree st c) && not hand.IsEmpty
            then let newCoord = if increment then incrementX c else decrementX c
                 hand |> List.map (fun x -> (x, Map.find x st.tiles) |> fun (z, t) -> let newWord = if increment then word@[(newCoord, (z, t))] else [(newCoord, (z, t))]@word
                                                                                      if wordExists st newWord && checkHorizontal st c word
                                                                                      then newWord 
                                                                                      else [])
                 |> List.filter (fun x -> x.Length > 0)
                 |> fun x -> let bestWord = findBestWord x
                             let index = if increment then bestWord.Length - 1 else 0
                             go (removeFirst (fun x -> x <> uint32 (snd (snd (snd (bestWord.[index]))))) hand) bestWord newCoord
       
            else word

        go (MultiSet.toList st.hand) word c

    let createWordVertical (st : State) (c : coord) (word : List<coord*(uint32*(char*int))>) (increment : bool) =
        let rec go (hand : List<uint32>) (word : List<coord*(uint32*(char*int))>) (c : coord)  =
            if (squareExistsAndFree st c) && not hand.IsEmpty
            then let newCoord = if increment then incrementY c else decrementY c
                 hand |> List.map (fun x -> (x, Map.find x st.tiles) |> fun (z, t) -> let newWord = if increment then [(newCoord, (z, t))]@word else word@[(newCoord, (z, t))]
                                                                                      if wordExists st newWord && checkVertical st c word
                                                                                      then newWord 
                                                                                      else [])
                 |> List.filter (fun x -> x.Length > 0)
                 |> fun x -> let bestWord = findBestWord x
                             let index = if increment then 0 else bestWord.Length - 1
                             go (removeFirst (fun x -> x <> uint32 (snd (snd (snd (bestWord.[index]))))) hand) bestWord newCoord
       
            else word

        go (MultiSet.toList st.hand) word c

     // First coord is already placed   
    let createWords (st : State) (first : coord*(uint32*(char*int))) = 
        let coordsToTryX = [incrementX (fst first); decrementX (fst first)]
        let coordsToTryY = [incrementY (fst first); decrementY (fst first)]

        let wordsHorizontal = List.map (fun x -> (createWordHorizontal st x [first] true)) coordsToTryX |> List.filter (fun x -> x.Length > 1) |> List.map (fun x -> x.[1..x.Length-1])
        let wordsVertical = List.map (fun x -> (createWordVertical st x [first] true)) coordsToTryY |> List.filter (fun x -> x.Length > 1)     |> List.map (fun x -> x.[0..x.Length-2])

        findBestWord (wordsHorizontal @ wordsVertical)



    let createWord (st : State) (word : List<coord*(uint32*(char*int))>) (c : coord) =
        let rec go hand word c =
            if wordExists st word
            then hand |> List.map (fun x -> (x, Map.find x st.tiles) |> fun (z, t) -> word@[(incrementX c, (z, t))]) 
                      |> List.filter (fun x -> x.Length > 0)
                      |> fun x -> let bestWord = findBestWord x
                                  go (removeFirst (fun x -> x <> uint32 (snd (snd (snd (bestWord.[0]))))) hand) bestWord (incrementX c)
            else word

        go (MultiSet.toList st.hand) word c


    let getStarterWords (st : State) =
       MultiSet.toList st.hand |> List.map (fun x -> (x, Map.find x st.tiles) |> fun (z, t) -> [(st.board.center, (z, t))]) 
       |> List.map (fun x -> createWord st x (st.board.center)) 



    // Find bounds of board?
    let findMove (st : State) =
        if fst st.lastPlayed.[0] = st.board.center then getStarterWords st |> findBestWord
        else st.lastPlayed |> List.map (fun t -> (createWords st t)) |> findBestWord
        

    // Add prefix and postfix
    // Search 
    let convertState b d pn h p lp t = {board = b; dict = d; playerNumber = pn; hand = h; played = p; lastPlayed = lp; tiles = t}

    let calcPoint (word : List<tile>) = failwith 