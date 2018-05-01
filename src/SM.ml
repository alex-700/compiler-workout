open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show

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

let take n l =
  let rec take' (acc, rest) = function
    | 0 -> (List.rev acc, rest)
    | n -> let v::rest = rest in take' (v::acc, rest) (n - 1) in
  take' ([], l) n

let rec eval env ((cstack, stack, con) as conf) =
  let flag = function
    | "z"  -> true
    | "nz" -> false
    | _    -> failwith "Bad conditional jump" in
  function
  | [] -> conf
  | stmt::prog ->
    let con', prog' = match stmt, stack, con with
      | BINOP op,    y::x::stack, _             ->
        (cstack, (Value.of_int @@ (Expr.op_of_string op) (Value.to_int x) (Value.to_int y))::stack, con), prog
      | CONST n,     _,           _             -> (cstack, Value.of_int n::stack, con),           prog
      | STRING s,    _,           _             -> (cstack, Value.of_string s::stack, con),        prog
      | LD v,        _,           (st, i, o)    -> (cstack, State.eval st v::stack, (st, i, o)),   prog
      | ST v,        n::stack,    (st, i, o)    -> (cstack, stack, (State.update v n st, i, o)),   prog
      | STA (v, n),  _,           (st, i, o)    ->
        let x::ids, stack = take (n + 1) stack in
        (cstack, stack, (Language.Stmt.update st v x (List.rev ids), i, o)), prog
      | LABEL _,     _,           _             -> conf, prog
      | JMP l,       _,           _             -> conf, (env#labeled l)
      | CJMP (f, l), n::stack,    _             ->
        (cstack, stack, con),
        (
          if flag f <> Expr.bool_of_int (Value.to_int n)
          then env#labeled l
          else prog
        )
      | CALL (l, n, p), _,        (st, _, _)    ->
        if env#is_label l
        then (((prog, st)::cstack, stack, con), (env#labeled l))
        else (env#builtin conf l n p), prog
      | BEGIN (_, args, locs), _, (st, i, o)    ->
        let rec build (acc : State.t) s a = match (s, a) with
          | _,     []    -> acc, s
          | v::s', x::a' -> build (State.update x v acc) s' a'
          | [],    _     -> failwith "few arguments on stack" in
        let st' = State.enter st (args @ locs) in
        let st'', stack' = build st' stack (List.rev args) in
        (cstack, stack', (st'', i, o)), prog
      | (END | RET _), _,         (st, i, o)    ->
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
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = take n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

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
    | Expr.Array es -> (List.concat (List.map compile_expr es)) @
                       [CALL ("$array", List.length es, true)]
    | Expr.String s -> [STRING s]
    | Expr.Var var -> [LD var]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]
    | Expr.Elem (a, i) -> compile_expr a @ compile_expr i @ [CALL ("$elem", 2, true)]
    | Expr.Length l -> compile_expr l @ [CALL ("$length", 1, true)]
    | Expr.Call (name, args) -> List.concat (List.map compile_expr args) @
                                [CALL (label_of_name name, List.length args, true)]
  in
  let rec compile' env = function
    | Stmt.Assign (var, [], expr) ->
      env, compile_expr expr @ [ST var]
    | Stmt.Assign (var, is, expr) ->
      env, (List.concat (List.map compile_expr is)) @
           compile_expr expr @
           [STA (var, List.length is)]
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
    | Stmt.Call (name, args) ->env, List.concat (List.map compile_expr args) @
                               [CALL (label_of_name name, List.length args, false)]
    | Stmt.Return None -> env, [RET false]
    | Stmt.Return (Some e) -> env, compile_expr e @ [RET true]
  and
    (>>) (env, l) e = env, l @ e
  and
    (>>.) (env, l) s = let env', l' = compile' env s in env', l @ l'
  in
  let compile_def env (name, (args, locs, body)) =
    (env, []) >> [LABEL (label_of_name name); BEGIN (name, args, locs)] >>. body >> [END] in
  let env, def_code = List.fold_left
      (
        fun (env, code) (name, decl) ->
          let env, code' = compile_def env (name, decl) in
          env, code @ code'
      )
      (new lenv, [])
      defs in
  (snd @@ (compile' env prog)) @ [END] @ def_code

