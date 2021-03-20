
(* ---- DECLARATION OF TYPES ---- *)
(* ide for variables *)
type ide = string

(* Acl to check if can do op *)
type acl = 
| Empty
| Acl of string * acl (* string is operation OR FUNCTION NAME *)

(* languages value *)
type exp = 
  | Eint of int
  | Ebool of bool
  | Var of ide
  | Plus of exp * exp (* + of Int * Int*)
  | Minus of exp * exp (* - of Int * Int*)
  | Mul of exp * exp (* * of Int * Int*)
  | Div of exp * exp (* / of Int * Int*)
  | Greater of exp * exp (* e1 > e2*)
  | Minor of exp * exp (* e1 < e2*)
  | Equals of exp * exp (* e1 == e2*)
  | IfThenElse of exp * exp * exp (* "guardia", then, else *)
  (* The following builder permits to give a name to an exp *)
  | Let of ide * exp * exp (* ide, value to associate to ide, body of let 
  i.e y (ide) = 5 (exp) in y + x (exp)  *)

  (* The following constructor indicates the Execution Monitor: 
  This is a local policy, its effected is 'inline' not global like Acl.
  The 3rd parameter 'acl' is the NEW LOCAL POLICY THAT COULD BE EXTEND THE GLOBAL ONE!
  Em monitor takes only a piece of code indicated by last operator (exp) WITH THE NEW SECURITY POLICY
  INDICATES BY 'acl'.
  It permits to give to variable 'ide' the value of 2nd operator (exp). *)
  | LetEm of ide * exp * acl * exp (* variable - value - new acl - expr to check by em *) 

  (* Fun is anonymous => it hasn't a name! 'ide' is the formal parameter!
  i.e f(x) = x + 1  => x is the formal parameter, x + 1 is the body*)
  | Fun of ide * exp  (* formal parameter with function body  Plus | Minus | Mul | Div *)
  | Call of exp * exp (* Fun with acutal parameter *)

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list
      
type value =
  | Int of int
  | Bool of bool
  | Func of string * exp * value env (* function name, body, env *)

(* ---- DECLARATION OF FUNCTIONS ---- *)

(* associate val with value to env *)
let bind (var: string) (value: value) (env: 'v env) =
  (var, value)::env

(* check if var has a assocviated value in the environment env *)
let rec lookup(env: 'v env) (var: string): value = match env with
  | [] -> failwith(var ^ " not found")
  | (ide, value)::envs -> 
    if (ide = var) then
      value
    else
      lookup envs var


(* verify if BASIC math op can be done or if the parametrized function can be executed
  (if it is in the Acl) *)
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
let rec eval (exp: exp) (env: 'v env) (acl: acl): value = match exp with
  | Eint x -> Int x
  | Ebool b -> Bool b
  | Var x -> lookup env x
  | IfThenElse(guardia, t, e) -> 
      begin match eval guardia env acl with (* evaluate guardia *)
      | Bool b -> 
        if (b) then
          eval t env acl (* ramo then *)
        else 
          eval e env acl (* ramo else *)
      | _ -> failwith("not a valid statement")
      end 
  | Plus(x, y) -> 
      (* check if sum is an operation permitted (occurs in Acl) *)
        if (check_op acl "+") then
          let x = eval x env acl in
          let y = eval y env acl in
          begin
          match (x, y) with
            | (Int x, Int y) ->
                (* check for integer overflow *)
                check_integer_overflow  x y;
                Int(x + y)
            | (_, _) -> failwith("Not int")
          end
        else failwith("Operation not supported")
  | Minus(x, y) -> 
      (* check if minus is an operation permitted (occurs in Acl) *)
        if (check_op acl "-") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) -> Int(x - y)
              | (_, _) -> failwith("Not int")
          end
        else failwith("Operation not supported")
  | Mul(x, y) -> 
      (* check if mul is an operation permitted (occurs in Acl) *)
        if (check_op acl "*") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) ->
                (* check for integer overflow *)
                check_integer_overflow x y;
                Int(x * y)
              | (_, _) -> failwith("Not int")
          end
        else failwith("Operation not supported")
  | Div(x, y) -> 
      (* check if div is an operation permitted (occurs in Acl) *)
        if (check_op acl "/") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) -> Int(x / y)
              | (_, _) -> failwith("Not int")
          end        
        else failwith("Operation not supported")
  | Greater(x, y) -> 
      (* check if > is an operation permitted (occurs in Acl) *)
        if (check_op acl ">") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) -> Bool(x > y)
              | (_, _) -> failwith("Not int")
          end        
        else failwith("Operation not supported")
  | Minor(x, y) -> 
      (* check if > is an operation permitted (occurs in Acl) *)
        if (check_op acl "<") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) -> Bool(x < y)
              | (_, _) -> failwith("Not int")
          end        
        else failwith("Operation not supported")
  | Equals(x, y) -> 
      (* check if == is an operation permitted (occurs in Acl) *)
        if (check_op acl "==") then
          begin
            match (eval x env acl, eval y env acl) with
              | (Int x, Int y) -> Bool(x = y)
              | (_, _) -> failwith("Not int")
          end        
        else failwith("Operation not supported")
  | Let(ide, value, body) ->
    (* "calculate" value ... *)
      let v = eval value env acl in 
      (* ... and bind this value to the ide for creating new env (new value on the stack).. *)
      let new_env = bind ide v env in
      (* check if v is a function that compare in the policies *)
        begin match v with 
        | Func(_, _, _) -> 
          if check_op acl ide then
            eval body new_env acl
          else 
            failwith ("This function cannot be called")
        | _ ->  eval body new_env acl (* ... and use it in the body *)
      end
  (* introduce local policy thanks to EM *)
  | LetEm(var, value, m_acl, monitor_exp) ->
      (* build new local policies extending global one *)
      let new_acl = extend_policies acl m_acl in
      (* evaluete value associated to var with new policies! *)
      let v = eval value env new_acl in
      (* extend also the environment adding new association between var and value!
      and then evaluate it with new policies *)
      eval monitor_exp (bind var v env) new_acl

  (* define functions*)
  | Fun(var, exp) -> 
    (* ---- WARNING ----
      var isn't the name of function! It is the argument, the formal parameter of function!
      i.e f (x) = x + 1   =>  var is x! Not the name of function! 
      For naming a function we must use the builder Let! 
      *)
      begin match exp with 
        | Plus(_, _) -> Func(var, exp, env)
        | Minus(_, _) -> Func(var, exp, env)
        | Mul(_, _) -> Func(var, exp, env)
        | Div(_, _) -> Func(var, exp, env)
        | _ -> failwith ("Ahah")
      end
  (* Call a function f with p actual parameter 
  i.e f(x) = x + 1 => f(5) = 6 *)
  | Call(f, param) -> 
      begin match f with
        | Fun(var, exp) -> 
          (* evaluate the ACTUAL parameter in the calling env *)
          let a_p = eval param env acl in
          (* bind the value of actual parameter to the formal parameter! *)
          let new_env = bind var a_p env in
          (* call the fucking function *)
          eval exp new_env acl
        | _ -> failwith("Not a function!")
      end

    
(* ---- "MAIN" ---- *)

(* declare an empty env *)
let empty_env = [];; (* val empty_env : 'a list = [] *)

(* the only op permitted is sum *)
let acl = Acl("+", Empty);;

let l = Let("y", Eint 5, Plus(Var "y", Var "x"));; 
eval l empty_env acl;; (* Exception: Failure "x not found" *)
(* this expression is equals to
let y = 5 in x + x;; => Error: Unbound value x *)

(* put a variable x in the env and try to do again the op *)
let env = bind "x" (Int 10) empty_env;; (* val env : (string * value) list = [("x", Int 10)]*)
let l = Let("y", Eint 5, Plus(Var "y", Var "x"));; 
eval l env acl;; (* value = Int 15 *)
(* this expression is equals to
let y = 5 in y + x;; => int = 15 *)

let l = Let("y", Eint 5, Plus(Var "y", Eint 10));; 
eval l empty_env acl;; (* value = Int 15 *)
(* this expression is equals to
let y = 5 in y + 10;; => int = 15 *)

let f = Fun("y", Plus(Var "y", Eint 20));; (* f (y) = y + 10 => ANONYMOUS (LAMDA) *)
eval f env acl;; (* value = Func ("y", Plus (Var "y"), Eint 20), [("x", Int 10)] THIS IS THE ENV IN THE MOMENT OF DECLARATION OF FUNCTION => THE VALUES IT KNOWS *)

let c = Call(f, Var "z");; (* val c : exp = Call (Fun ("y", Plus (Var "y", Eint 20)), Var "z" => ACTUAL PARAMETER, THE ARGUMENT OF F)*)
eval c env acl;; (* Exception: Failure "z not found" *)

let c = Call(f, Var "x");; (* val c : exp = Call (Fun ("y", Plus (Var "y", Eint 20)), Var "x" => ACTUAL PARAMETER, THE ARGUMENT OF F)*)
eval c env acl;; (* value = Int 30 *)

let f_let = Let("f", Fun("y", Plus(Var "y", Eint 20)), Call(f, Var "x"));;
(* let f y = y + 20 in f x;; where x is 30 *)
eval f_let env acl;; (* Exception: Failure "This function cannot be called" *)
(* add f to the policies *)
eval f_let env (Acl("f", acl));; (* value = Int 10 *)

eval (IfThenElse(Greater(Var "x", Eint 5), Eint 10, Eint 20)) env (Acl(">", acl));;
(* value = Int 10 *)