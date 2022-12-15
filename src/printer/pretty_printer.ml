open Core
open Bindlib
open  Printf
open Term
module T=Term

type layer =
|Zero
|Succ : layer -> layer
|Plus : layer * layer -> layer
|Var of layer Bindlib.var


and lterm = 
| Vari of ltvar * layer
| Type of layer
| Kind of layer
| Symb of sym
| Prod of lterm * ltbinder * layer
| Abst of lterm * ltbinder * layer
| Appl of lterm * lterm * layer
| Meta of meta * lterm array * layer
| Patt of int option * string * term array
| TEnv of lterm_env * lterm array
| Wild
| Plac of bool
| TRef of term option ref
| LLet of term * term * tbinder

and ltbinder = (lterm, lterm) Bindlib.binder

and ltmbinder = (lterm, lterm) Bindlib.mbinder

and ltvar = (lterm) Bindlib.var

and ltbox = lterm box

and lterm_env = 
  | TE_Vari of ltevar
  | TE_Some of ltmbinder
  | TE_None

and ltebox = lterm_env Bindlib.box

and ltevar = lterm_env Bindlib.var

(** On match la règle sur le term non layeré dnc on reprend le type rule de term.ml *)

let rec pretty_print : T.term -> string = function
  |Vari v -> name_of v
  |Type -> "TYPE"
  |Kind -> "KIND"
  |Symb s -> s.sym_name
  |Prod (t,tb) -> sprintf "(Π %s : %s.%s)" (name_of (fst(unbind tb))) (pretty_print t) (pretty_print (snd(unbind tb)))
  |Abst (t,tb) -> sprintf "(λ %s : %s.%s)" (name_of (fst(unbind tb))) (pretty_print t) (pretty_print (snd(unbind tb)))
  |Appl (t1,t2) -> sprintf "(%s %s)" (pretty_print t1) (pretty_print t2)
  |Plac b -> if b then "" else "false"
  |_ -> "bizarre"

let mk_free : layer -> ltvar -> lterm = fun l x -> Vari (x,l)

(**Boxing function*)
let lvar : ltvar -> lterm box = 
  fun x -> box_var x
let box_type : layer -> lterm box =
  fun l -> box (Type l)
let box_kind : layer -> ltbox = 
  fun l -> box (Kind l)
let pre_prod_abst : layer -> ltbox -> ltbinder box -> ltbox = fun l ->
  box_apply2 (fun a b -> Prod(a,b,l))
let prod : ltbox -> ltbinder box -> layer -> ltbox = fun a b l -> pre_prod_abst l a b
let abst : ltbox -> ltbinder box -> layer -> ltbox = fun t b l -> pre_prod_abst l t b
let appl : ltbox -> ltbox -> layer -> ltbox = 
  fun t u l -> box_apply2 (fun t u -> Appl (t,u,l)) t u
let symb : sym -> ltbox = fun s -> Bindlib.box (Symb s)
let box_meta : meta -> ltbox array -> layer -> ltbox = 
  fun m ts l -> Bindlib.box_apply (fun ts -> Meta(m,ts,l)) (box_array ts)
let patt : int option -> string -> tbox array -> ltbox =
  fun i n ts -> box_apply (fun ts -> Patt(i,n,ts)) (box_array ts)
let mk_LTEnv : lterm_env*lterm array -> lterm = fun (te,ts) ->
  match te with 
  |TE_Some mb -> Bindlib.msubst mb ts
  | _ -> TEnv (te,ts)
let tenv : ltebox -> ltbox array -> ltbox =
  fun te ts -> box_apply2 (fun te ts -> mk_LTEnv(te,ts)) te (Bindlib.box_array ts)

let rec box_lterm : lterm -> ltbox = function
  |Vari (x,_ ) -> lvar x 
  |Type l -> box_type l
  |Kind l -> box_kind l
  |Symb s -> symb s
  |Prod (t,b,l) -> prod (box_lterm t) (box_binder box_lterm b) l
  |Abst (t,b,l) -> abst (box_lterm t) (box_binder box_lterm b) l
  |Appl (t,u,l) -> appl (box_lterm t) (box_lterm u) l
  |Meta (m,a,l) -> box_meta m (Array.map box_lterm a) l
  |Patt (i,s,ts) -> patt i s (Array.map lift ts)
  |TEnv (te,ts) -> tenv (lift_lterm_env te) (Array.map box_lterm ts)
  |_ -> failwith "couldn't box"

and lift_lterm_env : lterm_env -> ltebox = function 
  | TE_Vari x -> Bindlib.box_var x
  | TE_None -> Bindlib.box TE_None
  | TE_Some _ -> assert false

and translate : term -> lterm = function
  |Vari x -> let x' = translate_var x Zero in Vari (x',Zero)
  |Type -> Type Zero
  |Kind -> Kind Zero
  |Symb s -> Symb s
  |_ -> failwith "Impossible to convert"
and translate_var : tvar -> layer -> ltvar = fun x l ->
  Bindlib.new_var (mk_free l) (name_of x)
and translate_tb : tbinder -> ltbinder = fun b ->
  let x,f = unbind b in
  let x' = translate_var x Zero in
  let f' = translate f in unbox (bind_var x' (box f'))
and translate_box : tbox -> ltbox = 
fun b -> box_apply translate b

