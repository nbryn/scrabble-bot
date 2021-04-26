namespace nbryn

module internal MoveGenerator =
    open ScrabbleUtil
    open MultiSet

    type State = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, (uint32*(char*int))>
        tiles         : Map<uint32, char*int>
        turns         : int
    }

    val findMove : State -> List<(coord * (uint32 * (char * int)))>
    val convertState : Parser.board -> Dictionary.Dict -> uint32 -> MultiSet<uint32> -> Map<coord, (uint32*(char*int))> -> Map<uint32, char*int> -> int -> State