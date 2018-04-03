(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
struct

  (* The type for expressions. Note, in regular OCaml there is no "@type..."
     notation, it came from GT.
  *)
  @type t =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * t * t with show

  (* Available binary operators:
      !!                   --- disjunction
      &&                   --- conjunction
      ==, !=, <=, <, >=, > --- comparisons
      +, -                 --- addition, subtraction
      *, /, %              --- multiplication, division, reminder
  *)

  (* State: a partial map from variables to integer values. *)
  type state = string -> int

  (* Empty state: maps every variable into nothing. *)
  let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

  (* Update: non-destructively "modifies" the state s by binding the variable x
     to value v and returns the new state.
  *)
  let update x v s = fun y -> if x = y then v else s y

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
    | _ ->
      let bool_op =
        match op with
        | ">" -> (>)
        | "<" -> (<)
        | ">=" -> (>=)
        | "<=" -> (<=)
        | "==" -> (=)
        | "!=" -> (<>)
        | "!!" -> (||) @.. bool_of_int
        | "&&" -> (&&) @.. bool_of_int
        | _ -> failwith "Unsupported operation" in
      int_of_bool @. bool_op

  (* Expression evaluator

        val eval : state -> t -> int
     Takes a state and an expression, and returns the value of the expression in
     the given state.
  *)
  let rec eval s = function
    | Const x -> x
    | Var x -> s x
    | Binop(op, l, r) -> (op_of_string op @.. eval s) l r

  (* Expression parser. You can use the following terminals:

       IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
       DECIMAL --- a decimal constant [0-9]+ as a string
  *)

  let construct_op s = fun x y -> Binop(s, x, y)

  (* I can't apply eta conversion here, because weak types cannot appear in translation units.
     Seriously, OCaml?
  *)
  let list_of_ops l = List.map (fun s -> (ostap ($(s)), construct_op s)) l

  ostap (
    primary: x:IDENT {Var x} | x:DECIMAL {Const x} | -"(" parse -")";
    parse: !(Ostap.Util.expr
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
    type config = State.t * int list * int list 

  (* The type of configuration: a state, an input stream, an output stream *)
  type config = Expr.state * int list * int list

  (* Statement evaluator

        val eval : config -> t -> config

     Takes a configuration and a statement, and returns another configuration
  *)
  let rec eval ((st, inp, out) as con) = function
    | Read var -> Expr.update var (List.hd inp) st, List.tl inp, out
    | Write expr -> st, inp, out @ [Expr.eval st expr]
    | Assign (var, expr) -> Expr.update var (Expr.eval st expr) st, inp, out
    | Seq (expr1, expr2) -> eval (eval con expr1) expr2
    | Skip -> con
    | If (expr1, stmt1, stmt2) ->
      eval con (if Expr.bool_of_int (Expr.eval st expr1) then stmt1 else stmt2)
    | (While (expr, stmt)) as wh  ->
      if Expr.bool_of_int (Expr.eval st expr)
      then eval (eval con stmt) wh
      else con
    | (Repeat (stmt, expr)) as rp ->
      let (st, _, _) as con = eval con stmt in
      if Expr.bool_of_int (Expr.eval st expr)
      then con
      else eval con rp

  let rec seq = function
    | [] -> Skip
    | hd::[] -> hd
    | hd::tl -> Seq(hd, seq tl) (* may be unnecessary*)
  let rec sum a b = match a with
    | Seq(x, y) -> Seq(x, sum y b)
    | _ -> Seq(a, b)
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
             %"od" { sum s1 @@ While (e, sum s3 s2) }
           | %"repeat" s:parse %"until" e:!(Expr.parse) { Repeat (s, e) };

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
      parse: empty {failwith "Not implemented"}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = failwith "Not implemented"
                                   
(* Top-level parser *)
let parse = Stmt.parse
