open GT
open Syntax

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
*)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)
let eval =
  let eval con stmt =
    match stmt, con with
    | BINOP op, (x::y::stack, scon) -> Expr.op_of_string op x y::stack, scon
    | CONST num, (stack, scon) -> num::stack, scon
    | READ, (stack, (st, num::inp, out)) -> num::stack, (st, inp, out)
    | WRITE, (num::stack, (st, inp, out)) -> stack, (st, inp, out @ [num])
    | LD var, (stack, (st, inp, out)) -> st var::stack, (st, inp, out)
    | ST var, (num::stack, (st, inp, out)) -> stack, (Expr.update var num st, inp, out)
    | _ -> failwith "Bad SM program" in
  List.fold_left eval

let rec compile_expr = function
  | Expr.Const num -> [CONST num]
  | Expr.Var var -> [LD var]
  | Expr.Binop (op, e1, e2) -> compile_expr e2 @ compile_expr e1 @ [BINOP op]

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile = function
  | Stmt.Read var -> [READ; ST var]
  | Stmt.Write expr -> compile_expr expr @ [WRITE]
  | Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
  | Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2

