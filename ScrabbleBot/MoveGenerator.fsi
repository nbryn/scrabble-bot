namespace nbryn

module internal MoveGenerator =
    open ScrabbleUtil
    open ScrabbleUtil.ServerCommunication
    open MultiSet

    type State = {
        board         : Parser.board
        dict          : Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, char*int>
        tiles         : Map<uint32, char*int>
        turns         : int
        failedPlays   : List<List<coord*(uint32*(char*int))>>
        invalidCoords : Set<coord>
    }

    val findMove     : State -> ServerMessage
    val convertState : Parser.board -> Dictionary.Dict -> uint32 -> MultiSet<uint32> -> 
                       Map<coord, char*int> -> Map<uint32, char*int> -> int -> 
                       List<List<coord*(uint32*(char*int))>> -> Set<coord> -> State