(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
  | Fact
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Divide
  | Equals
  | LessThan
  | GreaterThan
  | Exponent
  | Mod
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Str of string                        (* strings *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var v -> SS.singleton v                        
  | Num _ | Bool _  | Float _ | Str _ -> SS.empty                                                 
  | Unop (_, e) -> free_vars e                 
  | Binop (_, e1, e2) -> SS.union (free_vars e1) (free_vars e2)     
  | Conditional (e1, e2, e3) ->  SS.union (SS.union (free_vars e1) 
                                 (free_vars e2)) (free_vars e3)
  | Fun (v, e) -> SS.remove v (free_vars e)                  
  | Let (v, e1, e2) -> SS.union (SS.remove v (free_vars e2)) (free_vars e1)         
  | Letrec (v, e1, e2) -> SS.union (SS.remove v (free_vars e1)) 
                          (SS.remove v (free_vars e2))           
  | Raise | Unassigned -> SS.empty                         
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
;;
  
(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname : unit -> varid =
	let suffix_num = ref 0 in
	fun () -> let new_var = "z" ^ string_of_int (!suffix_num) in
		     suffix_num := !suffix_num + 1;
		     new_var ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let rec var_check (exp : expr) = 
    match exp with 
    | Var v -> if v = var_name then repl else exp                     
    | Num _ | Bool _ | Float _ | Str _ -> exp               
    | Unop (u, e) -> Unop (u, var_check e)      
    | Binop (b, e1, e2) -> Binop (b, var_check e1, var_check e2)  
    | Conditional (e1, e2, e3) -> Conditional (var_check e1, var_check e2, var_check e3)
    | Fun (v, e) -> if v = var_name then exp
                    else 
                      if SS.mem v (free_vars repl) then
                        let var_new = new_varname () in
                        Fun (var_new, var_check (subst v (Var var_new) e))
                      else
                        Fun(v, var_check e)
    | Let (v, e1, e2) ->  if v = var_name then Let (v, var_check e1, e2)
                          else 
                            if SS.mem v (free_vars repl) then
                              let var_new = new_varname () in
                              Let (var_new, var_check e1, var_check (subst v (Var var_new) e2))
                            else
                              Let (v, var_check e1, var_check e2)
    | Letrec (v, e1, e2) -> if v = var_name then
                              exp
                            else
                              if SS.mem v (free_vars repl) then
                                let var_new = new_varname () in
                                Letrec (var_new, var_check (subst v (Var var_new) e1), 
                                        var_check (subst v (Var var_new) e2))
                              else 
                                Letrec (v, var_check e1, var_check e2)
    | Raise | Unassigned -> exp
    | App (e1, e2) -> App (var_check e1, var_check e2)
  in
  var_check exp ;;

(*......................................................................
  String representations of expressions
 *)

(* Helper functions for binops and unops in absrt and concrete strings *) 

let string_of_unop (u : unop) : string = 
  match u with
  | Negate -> "~-"
  | Fact -> "!"
;;

let absrt_string_of_unop (u : unop) : string = 
  match u with
  | Negate -> "Negate"
  | Fact -> "Fact"
;;

let string_of_binop (bin : binop) : string = 
  match bin with
  | Plus -> "+" 
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | Equals -> "="
  | LessThan -> "<"
  | GreaterThan -> ">"
  | Exponent -> "^"
  | Mod -> "%"
;;   

let absrt_string_of_binop (bin : binop) : string = 
  match bin with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Divide -> "Divide"
  | Equals -> "Equals"
  | LessThan -> "LessThan"
  | GreaterThan -> "GreaterThan"
  | Exponent -> "Exponent"
  | Mod -> "Mod"
;;  

let space : string = " " ;;
    
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
	match exp with 
	| Var v -> v                       
	| Num n -> string_of_int n
  	| Float f -> string_of_float f                          
	| Bool b -> string_of_bool b 
  	| Str s -> s                     
  	| Unop (u, e) -> string_of_unop u ^ exp_to_concrete_string e 
  	| Binop (b, e1, e2) -> "(" ^ exp_to_concrete_string e1 ^ space ^ 
  						           string_of_binop b ^ space ^ 
  						           exp_to_concrete_string e2 ^ ")"
  	| Conditional (e1, e2, e3) -> "if" ^ exp_to_concrete_string e1 ^
                                space ^ "then" ^ exp_to_concrete_string e2 ^
                                space ^ "else" ^ exp_to_concrete_string e3   
  	| Fun (v, e) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string e 
  	| Let (v, e1, e2) -> "let " ^ v ^ " = " ^ exp_to_concrete_string e1 ^ 
  						         " in " ^ exp_to_concrete_string e2 
  	| Letrec (v, e1, e2) -> "let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 ^ 
  					              " in " ^ exp_to_concrete_string e2  
  	| Raise -> "Raise"
  	| Unassigned -> "Unassigned"
  	| App (e1, e2) -> exp_to_concrete_string e1 ^ space ^ 
  				          exp_to_concrete_string e2
;;

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
	match exp with
	| Var v -> "Var(" ^ v ^ ")" 
	| Num n -> "Num(" ^ string_of_int n ^ ")" 
  	| Float f -> "Float(" ^ string_of_float f ^ ")"  
	| Bool b -> "Bool(" ^ string_of_bool b ^ ")" 
  	| Str s -> "String(" ^ s ^ ")" 
	| Unop (u, e) -> "Unop(" ^ absrt_string_of_unop u ^ "," ^ 
                   space ^ exp_to_abstract_string e ^ ")" 
  	| Binop (b, e1, e2) -> "Binop(" ^ absrt_string_of_binop b ^ "," ^ 
                         space ^ exp_to_abstract_string e1 ^ 
                         "," ^ space ^ exp_to_abstract_string e2 ^ ")" 
  	| Conditional (e1, e2, e3) -> "Conditional(" ^ exp_to_abstract_string e1 ^
                                "," ^ space ^ exp_to_abstract_string e2 ^
                                "," ^ space ^ exp_to_abstract_string e3 ^ 
                                ")" 
  	| Fun (v, e) -> "Fun(" ^ v ^ "," ^ space ^ exp_to_abstract_string e ^ 
  	  				      ")"                 
  	| Let (v, e1, e2) -> "Let(" ^ v ^ "," ^ space ^ 
    					         exp_to_abstract_string e1 ^ "," ^ space ^ 
    					         exp_to_abstract_string e2 ^ ")"       
  	| Letrec (v, e1, e2) -> "Letrec(" ^ v ^ "," ^ space ^ 
    						          exp_to_abstract_string e1 ^ "," ^ 
    						          space ^ exp_to_abstract_string e2 ^ ")"         
  	| Raise -> "Raise"                               
  	| Unassigned -> "Unassigned"                          
  	| App (e1, e2) -> "App(" ^ exp_to_abstract_string e1 ^ "," ^ 
                    space ^ exp_to_abstract_string e2 ^ ")" 
;;
