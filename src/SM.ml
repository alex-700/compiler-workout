open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)

let debug = false

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

type config = (prg * State.t) list * Value.t list * Expr.config

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
    let con', prog' =
      if debug then begin
        print_string @@ "stack: " ^ String.concat "|" (List.map (show(Value.t)) stack);
        print_string "\n";
        print_string ("insn: " ^ show(insn) stmt);
        print_string "\n";
      end;
      match stmt, stack, con with
      | BINOP op,    y::x::stack, _             ->
        (cstack, (Value.of_int @@ (Expr.op_of_string op) (Value.to_int x) (Value.to_int y))::stack, con), prog
      | CONST n,     _,           _             -> (cstack, Value.of_int n::stack, con),           prog
      | STRING s,    _,           _             -> (cstack, Value.of_string s::stack, con),        prog
      | SEXP (n, cnt), _,         _             ->
        let elems, stack = take cnt stack in
        (cstack, Value.sexp n (List.rev elems)::stack, con), prog
      | LD v,        _,           (st, i, o)    -> (cstack, State.eval st v::stack, (st, i, o)),   prog
      | ST v,        n::stack,    (st, i, o)    -> (cstack, stack, (State.update v n st, i, o)),   prog
      | STA (v, n),  x::stack,           (st, i, o)    ->
        let ids, stack = take n stack in
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
      | DROP, _::stack, _ -> (cstack, stack, con), prog
      | DUP, x::stack, _ -> (cstack, x::x::stack, con), prog
      | SWAP, x::y::stack, _ -> (cstack, y::x::stack, con), prog
      | TAG s, x::stack, _ ->
        let res = Expr.int_of_bool (match x with Value.Sexp (name, _) -> name = s | _ -> false) in
        (cstack, Value.of_int res::stack, con), prog
      | ENTER vars, stack, (st, i, o) ->
        let es, stack = take (List.length vars) stack in
        let nst = List.fold_left2 (fun x y z -> State.bind y z x) State.undefined vars (List.rev es) in
        (cstack, stack, (State.push st nst vars, i, o)), prog
      | LEAVE, _, (st, i, o) -> (cstack, stack, (State.drop st, i, o)), prog
      | _ -> failwith ("Bad SM program: " ^ ( GT.transform(insn) (new @insn[show]) () stmt)) in
    eval env con' prog'

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)

let run p i =
  if debug then print_prg p;
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
           let stack'' = if (not p) then stack' else let Some r = r in r::stack' in
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

let label_of_name = (^) "L"

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
                       [CALL (".array", List.length es, true)]
    | Expr.String s -> [STRING s]
    | Expr.Sexp (name, es) -> (List.concat (List.map compile_expr es)) @
                                [SEXP (name, List.length es)]
    | Expr.Var var -> [LD var]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]
    | Expr.Elem (a, i) -> compile_expr a @ compile_expr i @ [CALL (".elem", 2, true)]
    | Expr.Length l -> compile_expr l @ [CALL (".length", 1, true)]
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
    | Stmt.Case (e, ps) ->
      let max_in_list = List.fold_left max 0 in
      let match_pattern env p =
        let rec calc_drops = function
          | Stmt.Pattern.Wildcard -> 0
          | Stmt.Pattern.Ident _ -> 0
          | Stmt.Pattern.Sexp (name, ps) -> 1 + (max_in_list @@ List.map calc_drops ps) in
        let drops_cnt = calc_drops p in
        if drops_cnt = 0
        then match p with
          | Stmt.Pattern.Wildcard -> env, [], [], [], []
          | Stmt.Pattern.Ident name -> env, [], [[DUP]], [name], []
          | Stmt.Pattern.Sexp (name, ps) -> failwith "wtf?"
        else
          let end_label, env = env#gen1 in
          let rec build_drops env = function
            | 0 -> env, [LABEL end_label], [end_label]
            | n ->
              let l, env' = env#gen1 in
              let env'', rest, restl = build_drops env' (n - 1) in
              env'', (LABEL l::DROP::rest), (l::restl) in
          let env, drops, dls = build_drops env (drops_cnt - 1) in
          let rec match_pattern' pat dls =
              (match pat with
              | Stmt.Pattern.Wildcard -> [], [], []
              | Stmt.Pattern.Ident name -> [], [[]], [name]
              | Stmt.Pattern.Sexp (name, ps) ->
                let lab::dls' = dls in
                let (_, a, b, c) = (List.fold_left
                   (fun (i, cs, bs, names) p ->
                      let cs', bs', names' = match_pattern' p dls' in
                      let ns = bs @ List.map (fun x -> CONST i::CALL(".elem", 2, true)::x) bs' in
                      i + 1, cs @ (DUP::CONST i::CALL(".elem", 2, true)::cs') @ [DROP], ns, names @ names'
                   )
                   (0, [DUP; TAG name; CJMP ("z", lab);
                        DUP; CALL(".length", 1, true); CONST (List.length ps); BINOP ("=="); CJMP("z", lab)], [], [])
                   ps) in
                (a, b, c)
              ) in
          let cs, bs, names = match_pattern' p (List.rev dls) in
          env, cs, List.map (fun x -> [DUP] @ x @ [SWAP]) bs, names, drops in
      let case_end, env = env#gen1 in
      let match_pattern_final env (p, s) =
        let env, cs, bs, names, drops = match_pattern env p in
        (env, [])                 >>
        cs                        >>
        [DUP] >> (List.concat bs) >>
        [DROP; ENTER names]       >>
        [DROP]                    >>.
        s                         >>
        [LEAVE; JMP (case_end)]   >>
        drops in
      let env, code = (List.fold_left  ((>>..) match_pattern_final) (env, compile_expr e) ps) in
      env, code @ [LABEL case_end]
    | Stmt.Call (name, args) ->env, List.concat (List.map compile_expr args) @
                               [CALL (label_of_name name, List.length args, false)]
    | Stmt.Return None -> env, [RET false]
    | Stmt.Return (Some e) -> env, compile_expr e @ [RET true]
    | Stmt.Leave -> env, [LEAVE]
  and
    (>>) (env, l) e = env, l @ e
  and
    (>>.) (env, l) s = let env', l' = compile' env s in env', l @ l'
  and
    (>>..) f (env, l) s = let env', l' = f env s in env', l @ l'
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

