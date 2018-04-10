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
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cstack, stack, con) as conf) =
  let flag = function
    | "z"  -> true
    | "nz" -> false
    | _    -> failwith "Bad conditional jump" in
  function
  | [] -> conf
  | stmt::prog ->
    let con', prog' = match stmt, stack, con with
    | BINOP op,    y::x::stack, _             -> (cstack, Expr.op_of_string op x y::stack, con), prog
    | CONST n,     _,           _             -> (cstack, n::stack, con),                        prog
    | READ,        _,           (st, n::i, o) -> (cstack, n::stack, (st, i, o)),                 prog
    | WRITE,       n::stack,    (st, i, o)    -> (cstack, stack, (st, i, o @ [n])),              prog
    | LD v,        _,           (st, i, o)    -> (cstack, State.eval st v::stack, (st, i, o)),   prog
    | ST v,        n::stack,    (st, i, o)    -> (cstack, stack, (State.update v n st, i, o)),   prog
    | LABEL _,     _,           _             -> conf, prog
    | JMP l,       _,           _             -> conf, (env#labeled l)
    | CJMP (f, l), n::stack,    _             ->
      (cstack, stack, con),
      (
        if flag f <> Expr.bool_of_int n
        then env#labeled l
        else prog
      )
    | CALL l,      _,           (st, _, _)    -> ((prog, st)::cstack, stack, con), (env#labeled l)
    | BEGIN (args, locs), _,    (st, i, o)    ->
      let rec build (acc : State.t) s a = match (s, a) with
        | _,     []    -> acc, s
        | v::s', x::a' -> build (State.update x v acc) s' a'
        | [],    _     -> failwith "few arguments on stack" in
      let st' = State.enter st (args @ locs) in
      let st'', stack' = build st' stack (List.rev args) in
      (cstack, stack', (st'', i, o)), prog
    | END,         _,           (st, i, o)    ->
      (match cstack with
      | (p', st')::cstack' -> (cstack', stack, (State.leave st st', i, o)), p'
      | _ -> conf, [])
    | _ -> failwith "Bad SM program" in
    eval env con' prog'

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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
let compile (defs, p) = failwith "Not implemented"

let label_of_name = (^) "l_"

class lenv =
  let name num = label_of_name (string_of_int num) in
  object
    val cnt = 0
    method gen2 = name cnt, name @@ cnt + 1, {< cnt = cnt + 2 >}
    method gen1 = name cnt, {< cnt = cnt + 1 >}
  end

let compile (defs, prog) =
  let rec compile_expr = function
    | Expr.Const num -> [CONST num]
    | Expr.Var var -> [LD var]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]
    | Expr.Call (name, args) -> List.concat (List.map compile_expr args) @ [CALL (label_of_name name)]
  in
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
    | Stmt.Call (name, args) ->
      env, compile_expr (Expr.Call (name, args))
    | Stmt.Return None -> env, [END]
    | Stmt.Return (Some e) -> env, compile_expr e @ [END]
  and
    (>>) (env, l) e = env, l @ e
  and
    (>>.) (env, l) s = let env', l' = compile' env s in env', l @ l'
  in
  let compile_def env (name, (args, locs, body)) =
    (env, []) >> [LABEL (label_of_name name); BEGIN (args, locs)] >>. body >> [END] in
  let env, def_code = List.fold_left
      (
        fun (env, code) (name, decl) ->
          let env, code' = compile_def env (name, decl) in
          env, code @ code'
      )
      (new lenv, [])
      defs in
  [LABEL "main"] @ (snd @@ (compile' env prog)) @ [END] @ def_code

