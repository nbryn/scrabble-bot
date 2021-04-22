namespace nbryn

open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open Parser

open System.IO

open ScrabbleUtil.DebugPrint

// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [x; y; id; c; p] ->
                    ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList

 module Print =

    let printHand pieces hand =
        hand |>
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, (char*int)>
        lastPlayed    : List<coord*(uint32*(char*int))>
        tiles         : Map<uint32, char*int>
    }

    let mkState b d pn h p lp t = {board = b; dict = d;  playerNumber = pn; hand = h; played = p; lastPlayed = lp; tiles = t}

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand

module internal MoveGen =

    let squareExist (st : State.state) (coord : coord) =
        match st.board.squares coord with
        | Some _ -> true
        | None   -> false

    let squareFree (st : State.state) (coord : coord) =
        match Map.tryFind coord st.played with
        | Some _ -> false
        | None   -> true

    let squareExistsAndFree (st : State.state) (coord : coord) =
        squareExist st coord && squareFree st coord

     
    let wordExists (st : State.state) (list : List<coord*(uint32*(char*int))>) =
        let word = List.map (fun (m, (x, (y, z))) -> y) list |> List.toArray |> System.String
        ScrabbleUtil.Dictionary.lookup word st.dict
   
    let incrementCoord (c : coord) (incrementX : bool) =
        if incrementX then ((fst c + 1, snd c)) else ((fst c, snd c + 1))

    let findBestWord (words : List<List<coord*(uint32*(char*int))>>) =
        words |> List.map (fun x -> List.fold (fun acc (_, (_, (_,z))) -> acc + z) 0 x)
        |> Seq.mapi (fun i v -> i, v) |> Seq.maxBy snd |> fun x -> words.[fst x]

     
    let rec removeFirst pred lst =
        match lst with
        | h::t when pred h -> t
        | h::t -> h::removeFirst pred t
        | _ -> []

    //Dont append to list - Might miss good words
    let createWord (st : State.state) (coord : coord) (word : List<coord*(uint32*(char*int))>) (incrementX : bool) =
        let rec go (hand : List<uint32>) (word : List<coord*(uint32*(char*int))>) (coord : coord)  =
            if (squareExistsAndFree st coord) && not hand.IsEmpty //need another check for adjacent squares
            then let newCoord = incrementCoord coord incrementX
                 hand |> List.map (fun x -> (x, Map.find x st.tiles) |> fun (z, t) -> if wordExists st ([(newCoord, (z, t))]@word) then [(newCoord, (z, t))]@word else [])
                 |> List.filter (fun x -> x.Length > 0)
                 |> fun x -> let bestWord = findBestWord x
                             go (removeFirst (fun x -> x <> uint32 (snd (snd (snd (bestWord.[bestWord.Length-1]))))) hand) bestWord newCoord
       
            else word

        go (MultiSet.toList st.hand) word coord
        
    let createWords (st : State.state) (first : coord*(uint32*(char*int))) = 
        let coordsToTryX = [first; first; first; first;] |> List.map (fun (x, _) -> (fst x + 1, snd x)) 
        let coordsToTryY = [first; first; first; first;] |> List.map (fun (x, _) -> (fst x, snd x + 1)) 

        let words1 = List.map (fun x -> (createWord st x [first] true)) coordsToTryX |> List.filter (fun x -> x.Length > 1)
        let words2 = List.map (fun x -> (createWord st x [first] true)) coordsToTryY |> List.filter (fun x -> x.Length > 1)

        failwith
        //findBestWord ((List.toSeq words1 |> List.concat) @ (List.concat words2))

    // Find bounds of board?
    let findMove (st : State.state) =
        if fst st.lastPlayed.[0] = st.board.center then failwith
        else let f = createWords st st.lastPlayed.[st.lastPlayed.Length - 1]
             failwith

    let calcPoint (word : List<tile>) = failwith 
module Scrabble =
    open System.Threading

    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)

            // remove the force print when you move on from manual input (or when you have learnt the format)
            forcePrint "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
            let input =  System.Console.ReadLine()
            let move = MoveGen.findMove st

            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            send cstream (SMPlay move)

            let msg = recv cstream
            debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let oldTiles = List.map (fun (_, (y, _)) -> (y, uint32 1)) ms

                let lastPlayed = List.map (fun (x, (y, _)) -> (x, (y, (Map.find y pieces)))) ms
                let played = Map.fold (fun acc key value -> Map.add key value acc) st.played (Map.ofList (List.map (fun (m, (x, (y, z))) -> (m, (y, z))) lastPlayed))
                
                let tempHand = List.fold (fun acc (x, _) -> MultiSet.removeSingle x acc) st.hand oldTiles
                let newHand = List.fold (fun acc (x, k) -> MultiSet.add x k acc) tempHand newPieces
                
                let newState = State.mkState st.board st.dict st.playerNumber newHand played lastPlayed st.tiles
                aux newState
            | RCM (CMPlayed (pid, ms, points)) ->
                (* Successful play by other player. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
            | RCM (CMPlayFailed (pid, ms)) ->
                (* Failed play. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st


        aux st

    let startGame 
            (boardP : boardProg) 
            (dictf : bool -> Dictionary.Dict) 
            (numPlayers : uint32) 
            (playerNumber : uint32) 
            (playerTurn  : uint32) 
            (hand : (uint32 * uint32) list)
            (tiles : Map<uint32, tile>)
            (timeout : uint32 option) 
            (cstream : Stream) =
        debugPrint 
            (sprintf "Starting game!
                      number of players = %d
                      player id = %d
                      player turn = %d
                      hand =  %A
                      timeout = %A\n\n" numPlayers playerNumber playerTurn hand timeout)

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        let dict = dictf false // Uncomment if using a trie for your dictionary
        let board = Parser.parseBoardProg boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        let convertTile (t : tile) = Set.toList t |> fun x -> x.[0]

        let t = Map.map (fun _ x -> convertTile x) tiles

        let h = convertTile (Map.find (uint32 1) tiles)

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet Map.empty [(board.center, (uint32 1, convertTile(Map.find (uint32 1) tiles)))] t) 