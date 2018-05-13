(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

(* Values *)
module Value =
struct

  @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

  let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

  let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

  let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

  let sexp   s vs = Sexp (s, vs)
  let of_int    n = Int    n
  let of_string s = String s
  let of_array  a = Array  a

  let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

  let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
  (*  let update_array  a i x = List.init   (List.length a)   (fun j -> if j = i then x else List.nth a j)*)
  (* O(length^2)? Seriously? *)
  let update_array a i x = List.mapi (fun j y -> if j = i then x else y) a

end


(* States *)
module State =
struct

  (* State: global state, local state, scope variables *)
  type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

  (* Undefined state *)
  let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

  (* Bind a variable to a value in a state *)
  let bind x v s = fun y -> if x = y then v else s y

  (* Empty state *)
  let empty = G undefined

  (* Update: non-destructively "modifies" the state s by binding the variable x
     to value v and returns the new state w.r.t. a scope
  *)
  let update x v s =
    let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
        if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
    in
    inner s

  (* Evals a variable in a state w.r.t. a scope *)
  let rec eval s x =
    match s with
    | G s -> s x
    | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

  (* Creates a new scope, based on a given state *)
  let rec enter st xs =
    match st with
    | G _         -> L (xs, undefined, st)
    | L (_, _, e) -> enter e xs

  (* Drops a scope *)
  let leave st st' =
    let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
    in
    let g = get st in
    let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
    in
    recurse st'

  (* Push a new local scope *)
  let push st s xs = L (xs, s, st)

  (* Drop a local scope *)
  let drop (L (_, _, e)) = e

end

(* Builtins *)
module Builtin =
struct

  let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String    s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array     a -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )
    | ".length"  -> (st, i, o, Some (Value.of_int
                                       (match List.hd args with
                                        | Value.Array a     -> List.length a
                                        | Value.String s    -> String.length s
                                        | Value.Sexp (_, a) -> List.length a
                                       )))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

end


let rec fold_map f c =
  function
  | []     -> c, []
  | hd::tl ->
    let a, c' = f c hd in
    let c'', l = fold_map f c' tl in
    c'', (a::l)

let default x = function
  | None -> x
  | Some a -> a

module Expr =
struct

  (* The type for expressions. Note, in regular OCaml there is no "@type..."
     notation, it came from GT.
  *)
  @type t =
  (* integer constant   *) | Const  of int
  (* array              *) | Array  of t list
  (* string             *) | String of string
  (* S-expressions      *) | Sexp   of string * t list
  (* variable           *) | Var    of string
  (* binary operator    *) | Binop  of string * t * t
  (* element extraction *) | Elem   of t * t
  (* length             *) | Length of t
  (* function call      *) | Call   of string * t list with show

  (* The type of configuration: a state, an input stream, an output stream, an optional value *)
  type config = State.t * int list * int list * Value.t option

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

     val eval : env -> config -> t -> config

     Takes an environment, a configuration and an expresion, and returns another configuration.
     The environment supplies the following method

     method definition : env -> string -> int list -> config -> config

     which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
     an returns a pair: the return value for the call and the resulting configuration
  *)
  let rec eval env ((st, i, o, r) as c) = function
    | Const x           -> (st, i, o, Some (Value.of_int x))
    | Array xs          -> eval' env c xs ".array"
    | String s          -> (st, i, o, Some (Value.of_string s))
    | Sexp (tag, xs)    ->
      let (st, i, o, vs) = eval_list env c xs in
      (st, i, o, Some (Value.sexp tag vs))
    | Var name          -> (st, i, o, Some (State.eval st name))
    | Binop (op, l, r)  ->
      let (st, i, o, Some l) as c = eval env c l in
      let (st, i, o, Some r) as c = eval env c r in
      (st, i, o, Some (Value.of_int (((op_of_string op) @.. Value.to_int) l r)))
    | Elem (l, r)       -> eval' env c [l; r] ".elem"
    | Length e          -> eval' env c [e] ".length"
    | Call (f, args)    -> eval' env c args f
   and eval_list env conf xs =
     let vs, (st, i, o, _) =
       List.fold_left
         (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
         )
         ([], conf)
         xs
     in
     (st, i, o, List.rev vs)
   and eval' env conf es name =
      let (st, i, o, args) = eval_list env conf es in
      env#definition env name args (st, i, o, None)

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

      base : x:DECIMAL { Const x }
    | -"[" es:!(Util.list0)[parse] -"]" { Array es }
    | s: STRING { String (String.sub s 1 (String.length s - 2))}
    | c: CHAR   { Const (Char.code c)}
    | "`" t: IDENT es: (-"(" !(Util.list0)[parse] -")")? { Sexp(t, default [] es) }
    | v: IDENT s: (
        a:(-"(" !(Util.list0)[parse] -")") { Call (v, a) }
      | empty { Var v }
      ) {s}
    | -"(" parse -")";
      primary : s: (
        b: base is: (-"[" i: parse -"]")* { List.fold_left (fun x y -> Elem (x, y)) b is }
      ) len:("." %"length")? { match len with None -> s | Some _ -> Length s };
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

  (* Patterns in statements *)
  module Pattern =
  struct

    (* The type for patterns *)
    @type t =
    (* wildcard "-"     *) | Wildcard
    (* S-expression     *) | Sexp   of string * t list
    (* identifier       *) | Ident  of string
    with show, foldl

    (* Pattern parser *)
    ostap (
      parse: empty {failwith "Not implemented"}
    )

    let vars p =
      transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
  end

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* leave a scope                    *) | Leave  with show

  (* The type of configuration: a state, an input stream, an output stream *)
  type config = State.t * int list * int list

  (* Statement evaluator

       val eval : env -> config -> t -> config

     Takes an environment, a configuration and a statement, and returns another configuration. The
     environment supplies the following method
         method definition : string -> (string list, string list, t)

     which returns a list of formal parameters, local variables, and a body for given definition
  *)

  let update st x v is =
  let rec update a v = function
    | []    -> v
    | i::tl ->
      let i = Value.to_int i in
      (match a with
       | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
       | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
      )
  in
  State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

  let rec (<+>) x y = match x, y with
    | Skip, _       -> y
    | _, Skip       -> x
    | Seq (l, r), _ -> l <+> (r <+> y)
    | _             -> Seq (x, y)

  let rec eval env ((st, i, o, r) as c) k stmt =
    let eval' = eval env in
    let evale = Expr.eval env in
    let evalec = evale c in
    let evaleci e =
      let (st, i, o, x) = evalec e in
      match x with
      | None -> failwith "Error"
      | Some x -> (st, i, o, Value.to_int x) in
    match stmt with
    | Skip ->
      (match k with
      | Skip -> c
      | _    -> eval' c Skip k)
    | Assign (n, is, e) ->
      let (st, i, o, is) = Expr.eval_list env c is in
      let (st, i, o, Some v) = Expr.eval env (st, i, o, None) e in
      eval' (update st n v is, i, o, None) Skip k
    | Seq (s1, s2) -> eval' c (s2 <+> k) s1
    | If (e, s1, s2) ->
      let (st, i, o, r) = evaleci e in
      eval' (st, i, o, None) k (if Expr.bool_of_int r then s1 else s2)
    | (While (e, s)) as wh ->
      let (st, i, o, r) = evaleci e in
      if Expr.bool_of_int r
      then eval' (st, i, o, None) (wh <+> k) s
      else eval' (st, i, o, None) Skip k
    | Repeat (s, e) -> eval' c ((While (Binop ("==", e, Const 0), s)) <+> k) s
    | Case (e, ps)  ->
      let (st, i, o, Some e_value) = evalec e in
      let (<+>) x y =
        match (x, y) with
        | _, None -> None
        | None, _ -> None
        | Some lx, Some ly -> Some (lx @ ly) in
      let rec match_pattern e p =
        (match (e, p) with
         | _, Pattern.Wildcard ->
           Some []
         | e, Pattern.Ident x ->
           Some [x, e]
         | Value.Sexp (e_s, e_es), Pattern.Sexp (p_s, p_es)
           when (e_s = p_s && List.length e_es = List.length p_es) ->
           List.fold_left2
             (fun x y z -> x <+> (match_pattern y z)) (Some []) e_es p_es
         | _ -> None) in
      let rec match_patterns = function
        | (h, next)::t ->
          (match (match_pattern e_value h) with
          | None -> match_patterns t
          | Some ms ->
            let ns = List.map fst ms in (* optimize here *)
            let nst = List.fold_left (fun x (y, z) -> State.bind y z x) State.undefined ms in
            eval' (State.push st nst ns, i, o, None) k (Seq(next, Leave)))
        | [] -> eval' (st, i, o, None) Skip k in
      match_patterns ps
    | Call (n, args) -> eval' (evalec (Expr.Call (n, args))) k Skip
    | Return None -> c
    | Return (Some e) -> (evalec e)
    | Leave -> eval' (State.drop st, i, o, None) Skip k

  (* Statement parser *)
  ostap (
    pattern: "_" { Pattern.Wildcard }
    | x:IDENT { Pattern.Ident x }
    | -"`" n:IDENT s: (-"(" !(Util.list0)[pattern] -")")? { Pattern.Sexp (n, default [] s) };
    case: pattern -"->" parse;
    primary:
      v:IDENT is: (-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) { Assign (v, is, e) }
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
      | %"case" e: !(Expr.parse) %"of" ps: !(Util.list0By)[ostap("|")][case] %"esac" { Case (e, ps) }
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
         "}" { ( name, (vars, default [] locs, body) )}
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left
                 (fun st (x, a) -> State.update x a st)
                 (State.enter st (xs @ locs))
                 (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap ( !(Definition.parse)* !(Stmt.parse) )

