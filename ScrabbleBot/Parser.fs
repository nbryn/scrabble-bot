module internal Parser

    open ScrabbleUtil
    open System
    open Eval
    open FParsecLight.TextParser
    
    
    let pIntToChar  = pstring "intToChar"
    let pPointValue = pstring "pointValue"

    let pCharToInt  = pstring "charToInt"
    let pToUpper    = pstring "toUpper"
    let pToLower    = pstring "toLower"
    let pCharValue  = pstring "charValue"

    let pTrue       = pstring "true"
    let pFalse      = pstring "false"
    let pIsDigit    = pstring "isDigit"
    let pIsLetter   = pstring "isLetter"

    let pif       = pstring "if"
    let pthen     = pstring "then"
    let pelse     = pstring "else"
    let pwhile    = pstring "while"
    let pdo       = pstring "do"
    let pdeclare  = pstring "declare"

    let whitespaceChar = satisfy (fun x -> System.Char.IsWhiteSpace x)
    let pletter        = satisfy (fun x -> System.Char.IsLetter x)
    let palphanumeric  = satisfy (fun x -> System.Char.IsLetterOrDigit x)

    let spaces         = many (pchar ' ')
    let spaces1        = many1 (pchar ' ')

    let (.>*>.) (p1 : Parser<'a>) (p2 : Parser<'b>) = p1 .>> spaces .>>. p2
    let (.>*>) (p1 : Parser<'a>) (p2 : Parser<'b>)  = p1 .>> spaces .>> p2
    let (>*>.) (p1 : Parser<'a>) (p2 : Parser<'b>)  = p1 .>> spaces >>. p2

    let parenthesise (p : Parser<'a>) = (((pstring "(" >>. spaces) >>. p) .>> spaces) .>> pstring ")"

    let convertToString (l : char list) = List.ofSeq l |> List.toArray |> System.String

    let pid = (pletter <|> pchar ('_')) .>>. (many palphanumeric .>>. many (pchar '_')) |>> fun (x, (y, z)) -> convertToString (x::y@z)

    
    let unop op a = (op .>> spaces) >>. a
    let binop op p1 p2 = (((p1 .>> spaces) .>> op) .>> spaces) .>>. p2

    let TermParse, tref = createParserForwardedToRef<aExp>()
    let ProdParse, pref = createParserForwardedToRef<aExp>()
    let AtomParse, aref = createParserForwardedToRef<aExp>()

    let TParse, href = createParserForwardedToRef<cExp>()

    let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
    let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"
    do tref := choice [AddParse; SubParse; ProdParse]

    let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
    let DivParse = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
    let ModParse = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"
    do pref := choice [MulParse; DivParse; ModParse; AtomParse]

    let ParParse       = parenthesise TermParse
    let NParse         = pint32 |>> N <?> "Int"
    let VParse         = pid |>> V <?> "String"
    let PVParse        = unop pPointValue AtomParse  |>> PV <?> "PV"
    let NegParse       = pchar '-' >>. pint32 |>> fun x -> Mul (N -1, N x)
    let CharToIntParse = pCharToInt .>>. spaces >>. parenthesise TParse |>> CharToInt <?> "CharToInt"
    do aref := choice [CharToIntParse; NegParse; PVParse; VParse; NParse; ParParse]

    let AexpParse = TermParse

    let PrParse        = parenthesise TParse
    let CParse         = pchar ''' >>. (pletter <|> pchar ' ') .>> pchar ''' |>> C <?> "C"
    let ToLowerParse   = pToLower .>>. spaces >>. PrParse |>> ToLower <?> "ToLower"
    let ToUpperParse   = pToUpper .>>. spaces >>. PrParse  |>> ToUpper <?> "ToUpper"
    let IntToCharParse = pIntToChar .>>. spaces >>. parenthesise AtomParse |>> IntToChar <?> "IntToChar"
    let CVParse        = unop (pCharValue) AtomParse |>> CV <?> "CV"
   
    do href := choice [IntToCharParse; ToLowerParse; ToUpperParse; CVParse; CParse; PrParse]

    let CexpParse = TParse

    let BTermParse, btref = createParserForwardedToRef<bExp>()
    let BProdParse, bpref = createParserForwardedToRef<bExp>()
    let BAtomParse, baref = createParserForwardedToRef<bExp>()


    let ConParse = binop (pstring "/\\" .>> many whitespaceChar) BProdParse BTermParse |>> Conj <?> "Conj"
    let DisParse = binop (pstring "\\/" .>> many whitespaceChar) BProdParse BTermParse |>> fun (x, y) -> Not (Conj (Not x, Not y))
    do btref := choice [ConParse; DisParse; BProdParse]

    let PrrParse            = parenthesise BTermParse
   
    let EqualParse          = binop (pchar '=') AtomParse AtomParse |>> AEq <?> "AEq"
    let NotEqualParse       = binop (pstring "<>") AtomParse AtomParse |>> fun x -> Not (AEq x)
    let LessParse           = binop (pchar '<') AtomParse AtomParse |>> ALt <?> "ALt"
    let GreaterParse        = binop (pchar '>') AtomParse AtomParse |>> fun x -> Conj (Not (AEq x), Not (ALt x))
    let GreaterOrEqualParse = binop (pstring ">=") AtomParse AtomParse |>> fun x -> Not (ALt x)
    let LessOrEqualParse    = binop (pstring "<=") AtomParse AtomParse |>> fun x -> Not (Conj ((Not (ALt x)), Not (Not (Not (AEq x)))))
    let IsLetter            = pIsLetter .>>. spaces >>. parenthesise TParse |>> IsLetter <?> "IsLetter"
    let IsDigit             = pIsDigit .>>. spaces >>. parenthesise TParse |>> IsDigit <?> "IsDigit"
    do bpref := choice [LessOrEqualParse; EqualParse; NotEqualParse; LessParse; GreaterParse; GreaterOrEqualParse; IsDigit; IsLetter; BAtomParse]

    let TrueParse           = pTrue |>> fun _ -> TT
    let FalseParse          = pFalse |>> fun _ -> FF
    let NotParse            = unop (pchar '~') BTermParse |>> Not <?> "Not"
    do baref := choice [NotParse; TrueParse; FalseParse; PrrParse;]
    
    let BexpParse = BTermParse

    let StmTermParse, stmref = createParserForwardedToRef<stm>()
    let StmProdParse, stmpref = createParserForwardedToRef<stm>()

    let SeqParse = binop (many whitespaceChar >>. pchar ';' .>> many whitespaceChar) StmProdParse StmTermParse |>> Seq
    do stmref := choice [SeqParse; StmProdParse] 

    let helper1 t s p = (((((many whitespaceChar >>. t) .>> spaces) >>. s) .>> spaces) .>> p) .>> spaces
    let helper2 = (((pchar '{' .>> many whitespaceChar) >>. StmTermParse) .>> many whitespaceChar) .>> pchar '}'

    let SkipParse  = pstring "" |>> fun _ -> Skip
    let ITParse    = helper1 pif BTermParse pthen .>>. helper2 .>> many whitespaceChar .>>. SkipParse |>> fun ((x, y), z) -> ITE (x, y, z)
    let ITEParse   = helper1 pif BTermParse pthen .>>. helper2 .>> many whitespaceChar .>> pelse .>> spaces .>> pchar '{' .>> spaces .>>. StmTermParse .>> spaces .>> pchar '}' |>> fun ((x, y), z) -> ITE (x, y, z)
    let WhileParse = helper1 pwhile BProdParse pdo .>>. helper2 |>> While
    let AssParse     = (((many whitespaceChar >>. pid .>> spaces) .>> pstring ":=") .>> spaces) .>>. TermParse |>> fun (x, y) -> Ass (string x, y)
    let DeclareParse = many whitespaceChar .>> pdeclare .>> spaces1 >>. pid |>> Declare
    do stmpref := choice [ITEParse; ITParse; WhileParse; AssParse; DeclareParse] 

    let stmntParse = StmTermParse

    type word   = (char * int) list
    type square = Map<int, word -> int -> int -> int>

    let parseSquareFun (sqp : squareProg) : square    = Map.map (fun _ y -> stmntToSquareFun (getSuccess (run stmntParse y))) sqp

    let parseBoardFun (s : string) (m : Map<int, 'a>) = getSuccess (run stmntParse s) |> fun x -> stmntToBoardFun x m

    type boardFun = coord -> square option
    type board = {
        center        : coord
        defaultSquare : square
        squares       : boardFun
        isInfinite    : bool
    }

    let parseBoardProg (bp : boardProg) : board = 
          {
         center = bp.center
         defaultSquare = parseSquareFun (Map.find bp.usedSquare bp.squares)
         squares = Map.map (fun _ y -> parseSquareFun y) bp.squares |> parseBoardFun bp.prog
         isInfinite = bp.isInfinite
        }



