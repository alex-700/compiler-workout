(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
  | R of int     (* hard register                    *)
  | S of int     (* a position on the hardware stack *)
  | M of string  (* a named memory location          *)
  | L of int     (* an immediate operand             *)

let string_of_opnd = function
  | R x -> regs.(x)
  | S x -> "S " ^ (string_of_int x)
  | M x -> "M " ^ x
  | L x -> string_of_int x

let string_of_stack l = "[" ^ (String.concat "|" (List.map string_of_opnd l)) ^ "]"

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
    | "+"   -> "addl"
    | "-"   -> "subl"
    | "*"   -> "imull"
    | "&&"  -> "andl"
    | "!!"  -> "orl"
    | "^"   -> "xorl"
    | "cmp" -> "cmpl"
    | _     -> failwith "unknown binary operator" in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

  Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let compile env =
  let mov r1 r2 = match r1, r2 with
    | R _, _ | _, R _ -> [Mov(r1, r2)]
    | _, _ -> [Mov (r1, eax); Mov (eax, r2)] in
  let compile env =
    let call env name n r =
      let name = match name.[0] with '.' -> "B" ^ (String.sub name 1 (String.length name - 1)) | _ -> name in
      let save_regs = List.map (fun x -> Push x) (env#live_registers n) in
      let load_regs = List.rev_map (fun x -> Pop x) (env#live_registers n) in
      let rev_args, env = env#popn n in
      let push_args = List.map (fun x -> Push x) rev_args in
      let push_args = match name with
        | "Barray" -> push_args @ [Push (L n)]
        | "Bsexp" -> push_args @ [Push (L n)]
        | "Bsta" -> let x::v::is = push_args in is @ [x; v; Push (L (n - 2))]
        | _ -> push_args in
      let result, env =
        (if r then let reg, env = env#allocate in [Mov(eax, reg)], env else [], env) in
      env,
      save_regs @
      push_args @
      [Call name; Binop ("+", L ((List.length push_args) * word_size), esp)] @
      load_regs @
      result
    in function
    | CONST n ->
      let s, env = env#allocate in
      env, [Mov (L n, s)]
    | STRING s ->
      let s, env = env#string s in
      let l, env = env#allocate in
      let env, call = call env ".string" 1 true in
      env, Mov (M ("$" ^ s), l) :: call
    | SEXP (t, n) ->
      let s, env = env#allocate in
      let env, code = call env ".sexp" (n + 1) true in
      env, [Mov (L env#hash t, s)] @ code
    | LD x ->
      let s, env = (env#global x)#allocate in
      env, mov (env#loc x) s
    | ST x ->
      let s, env = (env#global x)#pop in
      env, mov s (env#loc x)
    | STA (x, n) ->
      let s, env = (env#global x)#allocate in
      let push = mov (env#loc x) s in
      let env, code = call env ".sta" (n + 2) false in
      env, push @ code
    | LABEL l -> (if env#is_barrier then (env#drop_barrier)#retrieve_stack l else env), [Label l]
    | JMP l -> (env#set_stack l)#set_barrier, [Jmp l]
    | CJMP (s, l) ->
      let r, env = env#pop in
      env#set_stack l, [Mov (r, eax); Binop ("&&", eax, eax); CJmp (s, l)] (* optimize it *)
    | BEGIN (name, args, locs) ->
      let env = env#enter name args locs in
      env, [Push ebp; Mov(esp, ebp); Binop("-", M ("$" ^ env#lsize), esp)]
    | END -> env, [
        Label env#epilogue;
        Mov (ebp, esp);
        Pop ebp;
        Ret;
        Meta (Printf.sprintf "\t.set\t%s,\t%d" env#lsize (env#allocated * word_size))
      ]
    | CALL (name, n, r) -> call env name n r
    | RET r ->
      (if r then
        let r, env = env#pop in
        env, [Mov(r, eax); Jmp env#epilogue]
      else
        env, [Jmp env#epilogue])
    | DROP -> snd env#pop, []
    | DUP ->
      let x = env#peek in
      let s, env = env#allocate in
      env, mov x s
    | SWAP ->
      let x, y = env#peek2 in
      env, [Push x; Push y; Pop x; Pop y]
    | TAG t ->
      let s, env = env#allocate in
      let env, code = call env ".tag" 2 true in
      env, [Mov (L env#hash t, s)] @ code
    | ENTER vs ->
      let env, code =
        List.fold_left
          (fun (env, code) v ->
             let s, env = env#pop in
             env, (mov s @@ env#loc v)::code
          )
          (env#scope @@ List.rev vs, [])
          (List.rev vs)
      in
      env, List.concat @@ List.rev code
    | LEAVE -> env#unscope, []
    | BINOP op ->
      let y, x, env = env#pop2 in
      let res, env = env#allocate in
      let suffix_of_op = function
        | ">"  -> "g"
        | ">=" -> "ge"
        | "<"  -> "l"
        | "<=" -> "le"
        | "==" -> "e"
        | "!=" -> "ne"
        | _ -> failwith "unknown comparison operator" in
      let cmp r1 r2 = Binop("cmp", r1, r2) in
      let zero r = Binop("^", r, r) in
      let i2b r1 r2 suf = [zero r2; cmp r1 r2; Set ("ne", suf)] in
      env, match op with
      | "+" | "-" | "*" ->
        [
          Mov (x, eax);
          Binop (op, y, eax);
          Mov (eax, res)
        ]
      | "/" | "%" ->
        [
          Mov (x, eax);
          Cltd;
          Mov (y, edi);
          IDiv edi;
          Mov ((if op = "/" then eax else edx), res)
        ]
      | ">" | ">=" | "<" | "<=" | "==" | "!=" ->
        [
          Mov (x, eax);
          zero edx;
          cmp y eax;
          Set (suffix_of_op op, "%dl");
          Mov (edx, res)
        ]
      | "!!" | "&&" ->
        i2b x eax "%al" @
        i2b y edx "%dl" @
        [Binop(op, edx, eax); Mov(eax, res)]
      | _ -> failwith "unknown binary operator" in
  List.fold_left
    (fun (e, o) i ->
       let (e', o') = compile e i in
       (e', o @
            (*[Meta (Printf.sprintf "# %s / stack = %s / locals = %s" (GT.show(SM.insn) i) e#show_stack e#show_locals)] @*)
            o')
    ) (env, [])

(* A set of strings *)
module S = Set.Make (String)

(* A map indexed by strings *)
module M = Map.Make (String)

(* Environment implementation *)

let list_init =
  let rec init' s x f =
    if x == 0 then [] else
      (f s)::(init' (s + 1) (x - 1) f) in
  init' 0

let make_assoc l =
  List.combine l (list_init (List.length l) (fun x -> x))

let rec take l = function
  | 0 -> [], l
  | n -> let a, b = take (List.tl l) (n - 1) in (List.hd l)::a, b

(* Environment implementation *)
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let make_assoc l i = List.combine l (list_init (List.length l) (fun x -> x + i)) in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)

(*    method show_stack =
      GT.show(GT.list) (GT.show(opnd)) stack
*)

    method show_stack = string_of_stack stack

    method show_locals = String.concat "; " @@ List.map
        (fun x ->
           "(" ^
           (String.concat " | " @@ List.map
             ( fun (x, y) ->
                 x ^ " -> " ^ (string_of_int y)
             )
             x
           ) ^ ")"
        )
        locals

    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}

    (* associates a stack to a label *)
    method set_stack l = {< stackmap = M.add l stack stackmap >}

    (* retrieves a stack for a label *)
    method retrieve_stack l =
      try {< stack = M.find l stackmap >} with Not_found -> self

    (* gets a name for a global variable *)
    method loc x =
      try S (assoc x locals)
      with Not_found ->
        try S (- (List.assoc x args)  -  1) with Not_found -> M ("global_" ^ x)

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
	      let rec allocate' = function
	       | []                            -> ebx          , 0
	       | (S n)::_                      -> S (n+1)      , n+2
	       | (R n)::_ when n < num_of_regs -> R (n+1)      , stack_slots
	       | _                             -> S static_size, static_size + 1 in
	    allocate' stack in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* pops n operands from the symbolic stack *)
    method popn n = let res, stack' = take stack n in res, {< stack = stack' >}

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets all string definitions *)
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots

    (* enters a function *)
    method enter f a l =
      let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

    (* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname

    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)

