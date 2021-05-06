namespace nbryn

module internal MoveGenerator =
    open ScrabbleUtil
    open ScrabbleUtil.ServerCommunication
    open MultiSet
    open Types

    val findMove     : State -> ServerMessage
    val convertState : Parser.board -> Dictionary.Dict -> MultiSet<uint32> -> 
                       Map<coord, char*int> -> Map<uint32, char*int> -> bool -> 
                       List<List<coord*(uint32*(char*int))>> -> State