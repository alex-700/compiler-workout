open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
*)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)
let eval =
  let eval con stmt =
    match stmt, con with
    | BINOP op, (y::x::stack, scon) -> Expr.op_of_string op x y::stack, scon
    | CONST num, (stack, scon) -> num::stack, scon
    | READ, (stack, (st, num::inp, out)) -> num::stack, (st, inp, out)
    | WRITE, (num::stack, (st, inp, out)) -> stack, (st, inp, out @ [num])
    | LD var, (stack, (st, inp, out)) -> st var::stack, (st, inp, out)
    | ST var, (num::stack, (st, inp, out)) -> stack, (Expr.update var num st, inp, out)
    | _ -> failwith "Bad SM program" in
  List.fold_left eval

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec compile_expr = function
    | Expr.Const num -> [CONST num]
    | Expr.Var var -> [LD var]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]
  in function
    | Stmt.Read var -> [READ; ST var]
    | Stmt.Write expr -> compile_expr expr @ [WRITE]
    | Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
    | Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2
