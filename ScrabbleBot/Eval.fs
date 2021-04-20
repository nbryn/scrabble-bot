module internal Eval

    open StateMonad

    (* Code for testing *)

    let hello = [('H', 4);('E', 1);('L', 1);('L', 1);('O', 1);] 
    let state = mkState [("x", 5); ("y", 42)] hello ["_pos_"; "_result_"]
    let emptyState = mkState [] [] []
    
    let add a b = failwith "Not implemented"      
    let div a b = failwith "Not implemented"      

    type aExp =
        | N of int
        | V of string
        | WL
        | PV of aExp
        | Add of aExp * aExp
        | Sub of aExp * aExp
        | Mul of aExp * aExp
        | Div of aExp * aExp
        | Mod of aExp * aExp
        | CharToInt of cExp

    and cExp =
       | C  of char  (* Character value *)
       | CV of aExp  (* Character lookup at word index *)
       | ToUpper of cExp
       | ToLower of cExp
       | IntToChar of aExp

    type bExp =             
       | TT                   (* true *)
       | FF                   (* false *)

       | AEq of aExp * aExp   (* numeric equality *)
       | ALt of aExp * aExp   (* numeric less than *)

       | Not of bExp          (* boolean not *)
       | Conj of bExp * bExp  (* boolean conjunction *)

       | IsLetter of cExp     (* check for letter *)
       | IsDigit of cExp      (* check for digit *)

    let (.+.) a b = Add (a, b)
    let (.-.) a b = Sub (a, b)
    let (.*.) a b = Mul (a, b)
    let (./.) a b = Div (a, b)
    let (.%.) a b = Mod (a, b)

    let (~~) b = Not b
    let (.&&.) b1 b2 = Conj (b1, b2)
    let (.||.) b1 b2 = ~~(~~b1 .&&. ~~b2)       (* boolean disjunction *)
    let (.->.) b1 b2 = (~~b1) .||. b2           (* boolean implication *) 
       
    let (.=.) a b = AEq (a, b)   
    let (.<.) a b = ALt (a, b)   
    let (.<>.) a b = ~~(a .=. b)
    let (.<=.) a b = a .<. b .||. ~~(a .<>. b)
    let (.>=.) a b = ~~(a .<. b)                (* numeric greater than or equal to *)
    let (.>.) a b = ~~(a .=. b) .&&. (a .>=. b) (* numeric greater than *)    
   
    let rec arithEval (a : aExp) : SM<int> =  
        match a with
        | WL          -> wordLength
        | N a         -> ret (a)
        | V exp       -> lookup exp
        | PV a        -> arithEval a >>= (fun t -> pointValue t)        
        | Add(a, b)   -> arithEval a >>= (fun t -> arithEval b >>= (fun x -> ret (t + x)))
        | Sub(a, b)   -> arithEval a >>= (fun t -> arithEval b >>= (fun x -> ret (t - x)))
        | Mul(a, b)   -> arithEval a >>= (fun t -> arithEval b >>= (fun x -> ret (t * x)))
        | Div(a, b)   -> arithEval a >>= (fun t -> arithEval b >>= (fun x -> if x = 0 then fail (DivisionByZero) else ret (t / x)))
        | Mod(a, b)   -> arithEval a >>= (fun t -> arithEval b >>= (fun x -> if x = 0 then fail (DivisionByZero) else ret (t % x)))
        | CharToInt a -> charEval a >>= (fun x -> ret (int x))   

    and charEval (c : cExp) : SM<char> = 
        match c with
        | C a         -> ret (a)
        | CV a        -> arithEval a >>= characterValue
        | ToUpper a   -> charEval a >>= (fun x -> ret (System.Char.ToUpper x))
        | ToLower a   -> charEval a >>= (fun x -> ret (System.Char.ToLower x))
        | IntToChar a -> arithEval a >>= (fun x -> ret (char x))      

    let rec boolEval (c : bExp) : SM<bool> =
        match c with
        | TT            -> ret (true)
        | FF            -> ret (false)
        | AEq(a, b)     -> arithEval a >>= (fun x -> arithEval b >>= (fun y -> ret (x = y)))
        | ALt(a, b)     -> arithEval a >>= (fun x -> arithEval b >>= (fun y -> ret (x < y)))
        | Not(a)        -> boolEval a >>= (fun x -> ret (not x))
        | Conj(a, b)    -> boolEval a >>= (fun x -> boolEval b >>= (fun y -> ret (x && y)))
        | IsLetter(a)   -> charEval a >>= (fun x -> ret (System.Char.IsLetter x))  
        | IsDigit(a)    -> charEval a >>= (fun x -> ret (System.Char.IsDigit x))


    type stm =                (* statements *)
    | Declare of string       (* variable declaration *)
    | Ass of string * aExp    (* variable assignment *)
    | Skip                    (* nop *)
    | Seq of stm * stm        (* sequential composition *)
    | ITE of bExp * stm * stm (* if-then-else statement *)
    | While of bExp * stm     (* while statement *)

    let rec stmntEval (stmnt : stm) : SM<unit> =
        match stmnt with
        | Declare s              -> declare s
        | Ass(a, b)              -> arithEval b >>= update a
        | Skip                   -> ret ()
        | Seq(stm1, stm2)        -> stmntEval stm1 >>>= stmntEval stm2
        | ITE(guard, stm1, stm2) -> boolEval guard >>= (fun x -> if x then push >>>= stmntEval stm1 >>>= pop else push >>>= stmntEval stm2 >>>= pop)
        | While(guard, stm)      -> boolEval guard >>= (fun x -> if x then push >>>= stmntEval stm >>>= pop >>= fun _ -> push >>>= stmntEval (While(guard, stm)) else ret ())

(* Part 3 (Optional) *)

    type StateBuilder() =

        member this.Bind(f, x)    = f >>= x
        member this.Return(x)     = ret x
        member this.ReturnFrom(x) = x
        member this.Delay(f)      = f ()
        member this.Combine(a, b) = a >>= (fun _ -> b)
        
    let prog = new StateBuilder()

    let arithEval2 a = failwith "Not implemented"
    let charEval2 c = failwith "Not implemented"
    let rec boolEval2 b = failwith "Not implemented"

    let stmntEval2 stm = failwith "Not implemented"

(* Part 4 *) 

    type word = (char * int) list
    type squareFun = word -> int -> int -> int // This has changed from Assignment 6

    // Refactor your implementation from Assignment 6 to remove the Result type and return 0 on failure.
    // Details are in the assignment.
    let stmntToSquareFun (stm : stm) =
         fun w pos acc -> 
            mkState [("_pos_", pos); ("_acc_", acc); ("_result_", 0)] w ["_pos_"; "_acc_"; "_result_"]
            |> fun s -> stmntEval stm >>>= lookup "_result_" |> fun x -> match evalSM s x with
                                                                         | Success (r) -> r
                                                                         | Failure (_) -> 0
    // Refactor your implementation from Assignment 6 to remove the Result type and return None on failure.
    // Also, make sure the funciton is polymorphic on the return type and the lookup map.
    // Details in the assignment.
    let stmntToBoardFun (stm : stm) (m : Map<int, 'a>) =
        fun (x,y) ->
        mkState [("_x_", x); ("_y_", y); ("_result_", 0)] [] ["_x_"; "_y_"; "_result_"]
        |> fun s -> stmntEval stm >>>= lookup "_result_" >>= (fun x -> ret (Map.tryFind x m)) |>
        fun m -> match evalSM s m with
                 | Success (r) -> r
                 | Failure (_) -> None