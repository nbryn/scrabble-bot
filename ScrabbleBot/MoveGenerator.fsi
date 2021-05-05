namespace nbryn

module internal MoveGenerator =
    open ScrabbleUtil
    open ScrabbleUtil.ServerCommunication
    open MultiSet

    type State = {
        board         : Parser.board
        dict          : Dictionary.Dict
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, char*int>
        tiles         : Map<uint32, char*int>
        placeCenter   : bool
        failedPlays   : List<List<coord*(uint32*(char*int))>>
    }

    val findMove     : State -> ServerMessage
    val convertState : Parser.board -> Dictionary.Dict -> MultiSet<uint32> -> 
                       Map<coord, char*int> -> Map<uint32, char*int> -> bool -> 
                       List<List<coord*(uint32*(char*int))>> -> State