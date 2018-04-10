(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

(* States *)
module State =
struct

  (* State: global state, local state, scope variables *)
  type t = { g : string -> int; l : string -> int; scope : string list }

  let empty' = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

  let update' s x v = fun y -> if x = y then v else s y

  (* Empty state *)
  let empty =
    { g = empty'; l = empty'; scope = [] }

  (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
  *)
  let update x v s =
    if List.mem x s.scope
    then { s with l = update' s.l x v }
    else { s with g = update' s.g x v }

  (* Evals a variable in a state w.r.t. a scope *)
  let eval s x = (if List.mem x s.scope then s.l else s.g) x

  (* Creates a new scope, based on a given state *)
  let enter ?(ls=empty') st xs = { g = st.g; l = ls; scope = xs }

  (* Drops a scope *)
  let leave st st' = { st' with g = st.g }

end

let rec fold_map f c =
  function
  | []     -> c, []
  | hd::tl ->
    let a, c' = f c hd in
    let c'', l = fold_map f c' tl in
    c'', (a::l)

module Expr =
struct

  (* The type for expressions. Note, in regular OCaml there is no "@type..."
     notation, it came from GT.
  *)
  @type t =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * t * t
  (* function call    *) | Call  of string * t list with show

  (* The type of configuration: a state, an input stream, an output stream, an optional value *)
  type config = State.t * int list * int list * int option

  (* Available binary operators:
      !!                   --- disjunction
      &&                   --- conjunction
      ==, !=, <=, <, >=, > --- comparisons
      +, -                 --- addition, subtraction
      *, /, %              --- multiplication, division, reminder
  *)
  let (@.) f g x y = f @@ g x y

  let (@..) f g x y = f (g x) (g y)

  let bool_of_int = (<>) 0

  let int_of_bool x = if x then 1 else 0

  let op_of_string op =
    match op with
    | "+" -> (+)
    | "-" -> (-)
    | "*" -> ( * )
    | "/" -> (/)
    | "%" -> (mod)
    | _   ->
      let bool_op =
        match op with
        | ">"  -> (>)
        | "<"  -> (<)
        | ">=" -> (>=)
        | "<=" -> (<=)
        | "==" -> (=)
        | "!=" -> (<>)
        | "!!" -> (||) @.. bool_of_int
        | "&&" -> (&&) @.. bool_of_int
        | _    -> failwith "Unsupported operation" in
      int_of_bool @. bool_op


  (* Expression evaluator

     val eval : env -> config -> t -> int * config

     Takes an environment, a configuration and an expresion, and returns another configuration.
     The environment supplies the following method

     method definition : env -> string -> int list -> config -> config

     which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
     an returns a pair: the return value for the call and the resulting configuration
  *)
  let rec eval env ((st, i, o, r) as c) = function
    | Const x           -> x, (st, i, o, Some x)
    | Var x             -> let res = State.eval st x in res, (st, i, o, Some res)
    | Binop (op, l, r)  ->
      let a, c' = eval env c l in
      let b, (st'', i'', o'', _) as c'' = eval env c' r in
      let res = op_of_string op a b in
      res, (st'', i'', o'', Some res)
    | Call (name, args) ->
      let c', l = fold_map (eval env) c args in
      let (st, i, o, Some r) as c'' = env#definition env name l c' in
      r, c''


  let construct_op s = fun x y -> Binop(s, x, y)

  (* I can't apply eta conversion here, because weak types cannot appear in translation units.
     Seriously, OCaml?
  *)
  let list_of_ops l = List.map (fun s -> (ostap ($(s)), construct_op s)) l

  (* Expression parser. You can use the following terminals:

     IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
     DECIMAL --- a decimal constant [0-9]+ as a string
  *)
  ostap (
  primary: name:IDENT s:(args: (-"(" !(Util.list0)[parse] -")") { Call (name, args) }
                      | empty { Var name } ) {s}
      | x:DECIMAL {Const x}
      | -"(" parse -")";
    parse: !(Util.expr
               (fun x -> x)
               [|
                 `Lefta, list_of_ops ["!!"];
                 `Lefta, list_of_ops ["&&"];
                 `Nona,  list_of_ops [">="; ">"; "<="; "<"; "=="; "!="];
                 `Lefta, list_of_ops ["+"; "-"];
                 `Lefta, list_of_ops ["*"; "/"; "%"]
               |]
               primary
            )
  )
end

(* Simple statements: syntax and sematics *)
module Stmt =
struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

  (* The type of configuration: a state, an input stream, an output stream *)
  type config = State.t * int list * int list

  (* Statement evaluator

       val eval : env -> config -> t -> config

     Takes an environment, a configuration and a statement, and returns another configuration. The
     environment supplies the following method
         method definition : string -> (string list, string list, t)

     which returns a list of formal parameters, local variables, and a body for given definition
  *)
  let rec (<+>) x y = match x, y with
    | Skip, _       -> y
    | _, Skip       -> x
    | Seq (l, r), _ -> l <+> (r <+> y)
    | _             -> Seq (x, y)

  let rec eval env ((st, i, o, r) as c) k stmt =
    let eval' = eval env in
    let evale = Expr.eval env in
    let evalec = evale c in
    match stmt with
    | Skip ->
      (match k with
      | Skip -> c
      | _    -> eval' c Skip k)
    | Assign (n, e) ->
      let r, (st, i, o, _) = evalec e in
      eval' (State.update n r st, i, o, None) Skip k
    | Write e ->
      let r, (st, i, o, _) = evalec e in
      eval' (st, i, o @ [r], None) Skip k
    | Read n ->
      eval' (State.update n (List.hd i) st, List.tl i, o, None) Skip k
    | Seq (s1, s2) -> eval' c (s2 <+> k) s1
    | If (e, s1, s2) ->
      let r, (st, i, o, _) = evalec e in
      eval' (st, i, o, None) k (if Expr.bool_of_int r then s1 else s2)
    | (While (e, s)) as wh ->
      let r, (st, i, o, _) = evalec e in
      if Expr.bool_of_int r
      then eval' (st, i, o, None) (wh <+> k) s
      else eval' (st, i, o, None) Skip k
    | Repeat (s, e) -> eval' c ((While (Binop ("==", e, Const 0), s)) <+> k) s
    | Call (n, args) ->
      let c', args = fold_map evale c args in
      eval' (env#definition env n args c') Skip k
    | Return None -> c
    | Return (Some e) -> snd (evalec e)

  let default x = function
    | None -> x
    | Some a -> a

  (* Statement parser *)
  ostap (
    primary: %"read"  "("  v:IDENT         ")" { Read v }
           | %"write" "("  e:!(Expr.parse) ")" { Write e }
           | v:IDENT  ":=" e:!(Expr.parse)     { Assign (v, e) }
           | %"if" e:!(Expr.parse) %"then" s:parse
             elif:( %"elif" !(Expr.parse) %"then" parse)*
             se: ( x:( %"else" parse )? { default Skip x } )
             %"fi"
             {
               List.fold_right (fun (e, s) s' -> If (e, s, s')) ((e, s)::elif) se
             }
           | %"skip" { Skip }
           | %"while" e:!(Expr.parse) %"do"
             s:parse
             %"od" { While (e, s) }
           | %"for" s1:parse "," e:!(Expr.parse) "," s2:parse %"do"
             s3:parse
             %"od" { s1 <+> (While (e, s3 <+> s2)) }
           | %"repeat" s:parse %"until" e:!(Expr.parse) { Repeat (s, e) }
           | name: IDENT "(" args:!(Util.list0)[Expr.parse] ")" { Call (name, args) }
           | %"return" x:!(Expr.parse)? { Return x };

    parse: !(Ostap.Util.expr
      (fun x -> x)
      [|
        `Righta, [ostap (";"), fun x y -> Seq(x, y)]
      |]
      primary
    )
  )
end

(* Function and procedure definitions *)
module Definition =
struct
  (* The type for a definition: name, argument list, local variables, body *)
  type t = string * (string list * string list * Stmt.t)

  ostap (
  arg : IDENT;
  parse: %"fun" name:IDENT "(" vars:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list0 arg))?
         "{"
         body:!(Stmt.parse)
         "}" { ( name, (vars, Stmt.default [] locs, body) )}
  )
end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o


(* Top-level parser *)
let parse = ostap ( !(Definition.parse)* !(Stmt.parse) )

