namespace nbryn

open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open Parser
open MoveGenerator

open System.IO

open ScrabbleUtil.DebugPrint
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
    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, char*int>
        tiles         : Map<uint32, char*int>
        turns         : int
        failedPlays   : List<List<coord*(uint32*(char*int))>>
        invalidCoords : Set<coord>
    }

    let mkState b d pn h p t tu fp ic = {board = b; dict = d; playerNumber = pn; hand = h; played = p; tiles = t; turns = tu; failedPlays = fp; invalidCoords = ic}

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand

module Scrabble =
    open System.Threading

    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)

            let move = findMove (convertState st.board st.dict st.playerNumber st.hand st.played st.tiles st.turns st.failedPlays st.invalidCoords)
            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move)
           
            match move with
            | SMPlay move   -> send cstream (SMPlay move)
            | SMChange move -> send cstream (SMChange move)
            
            let msg = recv cstream
            debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move)

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let oldTiles = List.map (fun (_, (y, _)) -> (y, uint32 1)) ms

                let lastPlayed = List.map (fun (x, (y, _)) -> (x, (y, (Map.find y pieces)))) ms
                let played = Map.fold (fun acc key value -> Map.add key value acc) st.played (Map.ofList (List.map (fun (m, (x, (y, z))) -> (m, (y, z))) lastPlayed))
                
                let tempHand = List.fold (fun acc (x, _) -> MultiSet.removeSingle x acc) st.hand oldTiles
                let newHand = List.fold (fun acc (x, k) -> MultiSet.add x k acc) tempHand newPieces
                
                let newState = State.mkState st.board st.dict st.playerNumber newHand played st.tiles (st.turns + 1) st.failedPlays st.invalidCoords
                aux newState
            | RCM (CMChangeSuccess(newPieces)) ->
                let newHand = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newPieces

                let newState = State.mkState st.board st.dict st.playerNumber newHand st.played st.tiles (st.turns + 1) st.failedPlays st.invalidCoords
                aux newState
            | RCM (CMPlayed (pid, ms, points)) ->
                let lastPlayed = List.map (fun (x, (y, _)) -> (x, (y, (Map.find y pieces)))) ms
                let played = Map.fold (fun acc key value -> Map.add key value acc) st.played (Map.ofList (List.map (fun (m, (x, (y, z))) -> (m, (y, z))) lastPlayed))
                
                let newState = State.mkState st.board st.dict st.playerNumber st.hand played st.tiles (st.turns + 1) st.failedPlays st.invalidCoords
                aux newState
            | RCM (CMPlayFailed (pid, ms)) ->          
                let st' = st
                aux st'
            | RCM (CMGameOver _) -> ()
            | RGPE err -> match move with
                          SMPlay move -> List.fold (fun st ele -> match ele with
                                                                  | GPEEmptyTile c           -> State.mkState st.board st.dict st.playerNumber st.hand st.played st.tiles st.turns st.failedPlays (Set.add c st.invalidCoords)
                                                                  | GPEWordNotInDictionary _ -> State.mkState st.board st.dict st.playerNumber st.hand st.played st.tiles st.turns ([move]@st.failedPlays) st.invalidCoords
                                                                  | GPEWordNotAdjacent _     -> State.mkState st.board st.dict st.playerNumber st.hand st.played st.tiles st.turns ([move]@st.failedPlays) st.invalidCoords
                                                                  | _                        -> st
                                                   ) st err

                        |> fun x -> aux x
                    
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

        let dict = dictf false
        let board = Parser.parseBoardProg boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        let convertTile (t : tile) = Set.toList t |> fun x -> x.[0]

        let t = Map.map (fun _ x -> convertTile x) tiles

        fun () -> playGame cstream t (State.mkState board dict playerNumber handSet (Map.ofList [(board.center,  convertTile(Map.find (uint32 3) tiles))]) t 0 [] Set.empty)