(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

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
end

(* Simple statements: syntax and sematics *)
module Stmt =
struct

  (* The type for statements *)
  @type t =
  (* read into the variable           *) | Read   of string
  (* write the value of an expression *) | Write  of Expr.t
  (* assignment                       *) | Assign of string * Expr.t
  (* composition                      *) | Seq    of t * t with show

  (* The type of configuration: a state, an input stream, an output stream *)
  type config = Expr.state * int list * int list

  (* Statement evaluator

        val eval : config -> t -> config

     Takes a configuration and a statement, and returns another configuration
  *)
  let rec eval (st, inp, out) = function
    | Read var -> Expr.update var (List.hd inp) st, List.tl inp, out
    | Write expr -> st, inp, out @ [Expr.eval st expr]
    | Assign (var, expr) -> Expr.update var (Expr.eval st expr) st, inp, out
    | Seq (expr1, expr2) -> eval (eval (st, inp, out) expr1) expr2
end

