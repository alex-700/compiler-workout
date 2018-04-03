open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST   of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let eval env ((cstack, stack, ((st, i, o) as c)) as conf) = failwith "Not implemented"

let rec eval env con =
  let flag = function
    | "z"  -> true
    | "nz" -> false
    | _    -> failwith "Bad conditional jump" in
  function
  | [] -> con
  | stmt::prog ->
    let ncon, nprog = match stmt, con with
    | BINOP op, (y::x::stack, scon) -> (Expr.op_of_string op x y::stack, scon), prog
    | CONST num, (stack, scon) -> (num::stack, scon), prog
    | READ, (stack, (st, num::inp, out)) -> (num::stack, (st, inp, out)), prog
    | WRITE, (num::stack, (st, inp, out)) -> (stack, (st, inp, out @ [num])), prog
    | LD var, (stack, (st, inp, out)) -> (st var::stack, (st, inp, out)), prog
    | ST var, (num::stack, (st, inp, out)) -> (stack, (Expr.update var num st, inp, out)), prog
    | LABEL _, _ -> con, prog
    | JMP label, _ -> con, (env#labeled label)
    | CJMP (f, label), (x::stack, scon) ->
      (stack, scon),
      (
        if flag f <> Expr.bool_of_int x
        then env#labeled label
        else prog
      )
    | _ -> failwith "Bad SM program" in
    eval env ncon nprog

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = failwith "Not implemented"s

class lenv =
  let name num = "label" ^ (string_of_int num) in
  object
    val cnt = 0
    method gen2 = name cnt, name @@ cnt + 1, {< cnt = cnt + 2 >}
    method gen1 = name cnt, {< cnt = cnt + 1 >}
  end

let compile prog =
  let rec compile_expr = function
    | Expr.Const num -> [CONST num]
    | Expr.Var var -> [LD var]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op] in
  let rec compile' env = function
    | Stmt.Read var -> env, [READ; ST var]
    | Stmt.Write expr -> env, compile_expr expr @ [WRITE]
    | Stmt.Assign (var, expr) -> env, compile_expr expr @ [ST var]
    | Stmt.Seq (stmt1, stmt2) -> (env, []) >>. stmt1 >>. stmt2
    | Stmt.Skip -> env, []
    | Stmt.If (e, s1, s2) ->
      let l1, l2, env = env#gen2 in
      (env, compile_expr e) >>
      [CJMP ("z", l1)]      >>.
      s1                    >>
      [JMP l2; LABEL l1]    >>.
      s2                    >>
      [LABEL l2]
    | Stmt.While (e, s) ->
      let l1, l2, env = env#gen2 in
      (env, [JMP l2; LABEL l1]) >>.
      s                         >>
      [LABEL l2]                >>
      compile_expr e            >>
      [CJMP ("nz", l1)]
    | Stmt.Repeat (s, e) ->
      let l1, env = env#gen1 in
      (env, [LABEL l1]) >>.
      s                 >>
      compile_expr e    >>
      [CJMP ("z", l1)]
  and
    (>>) (env, l) e = env, l @ e
  and
    (>>.) (env, l) s = let env', l' = compile' env s in env', l @ l'
  in
  snd @@ (compile' (new lenv) prog)
