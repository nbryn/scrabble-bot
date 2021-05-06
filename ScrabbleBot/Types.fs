namespace nbryn

module internal Types =
    open ScrabbleUtil

     type State = {
        board         : Parser.board
        dict          : Dictionary.Dict
        hand          : MultiSet.MultiSet<uint32>
        played        : Map<coord, char*int>
        tiles         : Map<uint32, char*int>
        placeCenter   : bool
        failedPlays   : List<List<coord*(uint32*(char*int))>>
    }

    type Surrounding = (bool*bool)*(bool*bool)