(* NOT POLIMORFIC LANGUAGE: THE ONLY POSSIBLE VALUES ARE INTEGERS! *)

(* ---- DECLARATION OF TYPES ---- *)
(* ide for variables *)
type ide = string

(* Acl to check if can do op *)
type acl = 
| Empty
| Acl of string * acl (* string is operation *)

(* languages value *)
type exp = 
  | Eint of int
  
  | Var of ide
  | Plus of exp * exp (* + of Int * Int*)
  | Minus of exp * exp (* - of Int * Int*)
  | Mul of exp * exp (* * of Int * Int*)
  | Div of exp * exp (* / of Int * Int*)

  (* The following constructor indicates the Execution Monitor: 
  This is a local policy, its effected is 'inline' not global like Acl.
  The 3rd parameter 'acl' is the NEW LOCAL POLICY THAT COULD BE EXTEND THE GLOBAL ONE!
  Em monitor takes only a piece of code indicated by last operator (exp) WITH THE NEW SECURITY POLICY
  INDICATES BY 'acl'.
  It permits to give to variable 'ide' the value of 2nd operator (exp).
    *)
  | LetEm of ide * exp * acl * exp (* variable - value - new acl - expr to check by em *) 
 (*  | Fun of ide * exp var * Plus | Minus | Mul | Div *)

(* environment is a couple list of ide with their value *)
type env = (string * int)list
      


(* ---- DECLARATION OF FUNCTIONS ---- *)

(* associate val with value to env *)
let bind (var: string) (value: int) (env: env) =
  (var, value)::env

(* check if var has a assocviated value in the environment env *)
let rec lookup(env: env) (var: string): int = match env with
  | [] -> failwith("association not found")
  | (ide, value)::envs -> 
    if (ide = var) then
      value
    else
      lookup envs var


(* verify if op can be done (if it is in the Acl) *)
let rec check_op (acl: acl) (op: string) = match acl with
| Empty -> false
| Acl (aop, acls) -> 
  if (aop = op) 
    then true
  else 
    check_op acls op

(* extend the GLOBAL ACL with LOCAL ACL introduced by EM *)
let rec extend_policies (global_acl: acl) (local_acl: acl) : acl =
   match local_acl with
   | Empty -> global_acl
   | Acl(op, acls) -> Acl(op, extend_policies global_acl acls)

   

(* extend the GLOBAL ACL with LOCAL ACL introduced by EM
let fast_extend_policies (global_acl: acl) (local_acl: acl) : acl =
  (* use power of recursion! *)
  let rec extend_policies_accum (local_acl: acl) : acl = 
    match local_acl with
   | Empty -> global_acl
   | Acl(op, acls) -> Acl(op, global_acl); extend_policies_accum acls
  in extend_policies_accum local_acl
 *)


(* ---- THE INTERPRETER ---- *)

(* check for integer overflow NOT COVER ALL CASE (not important for now) *)
let check_integer_overflow(x: int) (y: int): unit = 
    (* if x > 0 && y > 0 and their sum is < 0 => integer overflow *)
  if (x > 0 && y > 0 && x + y < 0) then
    failwith("Integer overflow detected: you can't hack this system")

(* evaluate my language: interpreter *)
let rec eval (exp: exp) (env: env) (acl: acl): int = match exp with
  | Eint x -> x
  | Var x -> lookup env x
  | Plus(x, y) -> 
      (* check if sum is an operation permitted (occurs in Acl) *)
        if (check_op acl "+") then
          let x = eval x env acl in
          let y = eval y env acl in
          (* check for integer overflow *)
          check_integer_overflow x y;
          x + y
        else failwith("Operation not supported")
  | Minus(x, y) -> 
      (* check if minus is an operation permitted (occurs in Acl) *)
        if (check_op acl "-") then
          eval x env acl - eval y env acl
        else failwith("Operation not supported")
  | Mul(x, y) -> 
      (* check if mul is an operation permitted (occurs in Acl) *)
        if (check_op acl "*") then
          eval x env acl * eval y env acl
        else failwith("Operation not supported")
  | Div(x, y) -> 
      (* check if div is an operation permitted (occurs in Acl) *)
        if (check_op acl "/") then
          eval x env acl / eval y env acl
        else failwith("Operation not supported")

  (* introduce local policy thanks to EM *)
  | LetEm(var, value, m_acl, monitor_exp) ->
    (* build new local policies extending global one *)
    let new_acl = extend_policies acl m_acl in
    (* evaluete value associated to var with new policies! *)
    let v = eval value env new_acl in
    (* extend also the environment adding new association between var and value!
    and then evaluate it with new policies *)
    eval monitor_exp (bind var v env) new_acl




(* ---- "MAIN" ---- *)

(* declare an empty and *)
let empty_env = [];; (* val empty_env : 'a list = [] *)

(* acl has no operation permitted *)
let acl = Empty;; (* val acl : acl = Empty*)

(* bind a value to env *)
let env = bind "x" 50 empty_env;; (* val env : (string * int) list = [("x", 50)] *)

(* evaluate 'x' in env *)
let x = eval(Var "x") env acl;; (* int = 5 *)

(* try to do sum -> raise exception because in Acl is empty *)
let s = eval(Plus(Eint x, Eint 19)) env acl;; (* Exception: Failure "Operation not supported" *)

(* add "+" (concat) operation to acl *)
let acl = Acl("+", acl);; (* val acl : acl = Acl ("+", Empty) *)

(* add all the others op in acl *)
let acl = Acl("/", Acl("-", acl));; (* val acl : acl = Acl ("/", Acl ("-", Acl ("+", Empty)))) *)

(* try now to do sum operation *)
let s = eval(Plus(Var "x", Eint 19)) env acl;; (* val s : int = 69 *)
let s = eval(Plus(Var "x", Eint (Int.max_int))) env acl;; 
(* Exception: Failure "Integer overflow detected: you can't hack this system" *)

(* try to do * operation *)
let p = eval(Mul(Var "x", Var "x")) env acl;; (* Exception: Failure "Operation not supported" *)

(* ---- now declare an EM that permits to do Mul op (LOCAL) ---- *)
(* First of all declare the policies! *) 
let policy = Acl("*", Empty);;

(* p will be linked to 'y' in last operator *)
let p = Mul(Var "x", Var "x");;
let em = eval(LetEm("y", p, policy,  p)) env acl;;