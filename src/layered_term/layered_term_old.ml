open Core
open Bindlib
open Term
module T=Term

type layer =
|Zero
|Succ : layer -> layer
|Plus : layer * layer -> layer
|Var of layer Bindlib.var


and lterm = 
| Vari of ltvar*layer
| Type
| Kind
| Symb of sym
| Prod of (lterm*layer) * (ltbinder)
| Abst of (lterm*layer) * (ltbinder)
| Appl of (lterm*layer) * (lterm*layer) * layer
(**| Meta of lmeta * lterm array*)

and ltbinder = (lterm*layer, lterm*layer) Bindlib.binder

and ltmbinder = (lterm, lterm) Bindlib.mbinder

and ltvar = (lterm * layer) Bindlib.var

and ltbox = (lterm*layer) box

and lmeta =   
{ meta_key   : int (** Unique key. *)
; meta_type  : term ref (** Type. *)
; meta_arity : int (** Arity (environment size). *)
; meta_value : ltmbinder option ref (** Definition. *) }

let rec compute : layer -> layer = fun l -> match l with
  |Zero -> Zero
  |Succ _ as t -> t
  |Var _ as t -> t
  |Plus (Zero,a) -> compute a
  |Plus (a,Zero) -> compute a
  |Plus (Succ a,b) -> Succ (compute (Plus (a,b)))
  |Plus (a, Succ b) -> Succ (compute (Plus (a,b)))
  |Plus ((Var _ as t), a) -> Plus (t,(compute a))
  |Plus (a, (Var _ as t)) -> Plus (compute a, t)
  |Plus (a,b) -> compute (Plus(compute a,compute b))

exception Sup of string

let rec sup_strict : layer -> layer -> bool = fun l1 l2 -> match (compute l1,compute l2) with 
  |Zero,Zero -> false
  |Succ a, Succ b -> sup_strict a b
  |Plus (Zero,a), Plus (Zero, b) -> sup_strict a b
  |Zero, Succ _ -> false
  |Succ _, Zero -> true
  |_ -> raise (Sup "You used a var in a layer, not supported for the current comp")

let rec eq : layer -> layer -> bool = fun l1 l2 -> match (compute  l1, compute l2) with
  |Plus (a,b) as l1,(Plus (c,d) as l2) -> l1 == l2 || Plus (b,a) == Plus (c,d)
  |Succ a, Succ b -> eq a b
  |a,b -> a==b

let sup : layer -> layer -> bool = fun l1 l2 -> eq l1 l2 || sup_strict l1 l2

let mk_free : layer -> ltvar -> lterm*layer = fun l x -> Vari (x,l),l
let var : ltvar -> ltbox = fun x -> Bindlib.box_var x
let box_type : layer -> ltbox = fun l -> box (Type,l)
let box_kind : layer -> ltbox = fun l -> box (Kind,l)
let box_symb : layer -> sym -> ltbox = fun l s -> Bindlib.box (Symb s, l)
let box_prod : layer -> (ltbox -> ltbinder Bindlib.box -> ltbox) = fun l ->
  Bindlib.box_apply2 (fun a b -> (Prod (a,b),l))
let box_abst : layer -> ltbox -> ltbinder Bindlib.box -> ltbox = fun l -> 
  Bindlib.box_apply2 (fun a b -> (Abst (a,b), l))
let box_appl : layer -> ltbox -> ltbox -> ltbox = fun l -> 
  Bindlib.box_apply2 (fun u v -> (Appl (u,v,l),l))

let rec box_lterm : (lterm*layer) -> ltbox = function
  |Vari (x,_),_ -> var x
  |Type,l -> box_type l
  |Kind,l -> box_kind l
  |Symb s,l -> box_symb l s
  |Prod (t,b),l -> box_prod l (box_lterm t) (box_binder box_lterm b)
  |Abst (t,b),l -> box_prod l (box_lterm t) (box_binder box_lterm b)
  |Appl (u,v,_),l -> box_appl l (box_lterm u) (box_lterm v)

  (**Besoin d'un contexte pour garder trace des variable créée*)
let rec term_to_lterm : term -> (int * ((lterm * layer) var*layer)) list -> lterm = fun t ctxt -> match t with 
  |Vari x -> begin try 
              let x,l = List.assoc (uid_of x) ctxt in Vari (x,l) 
              with _ -> Vari ((Bindlib.new_var (mk_free Zero) (name_of x)),Zero)
            end
  |Type -> Type
  |Kind -> Kind
  |Symb s -> Symb s
  |Prod (t,b) -> let x,f = unbind b in 
                 let id = uid_of x in
                 let x = Bindlib.new_var (mk_free Zero) (name_of x) in 
                 let f = term_to_lterm f ((id,(x,Zero))::ctxt) in
                 let b = unbox (bind_var x (box_lterm (f,Zero))) in
                 let t = term_to_lterm t ctxt in
                 Prod ((t,Zero),b)
  |Abst (t,b) -> let x,f = unbind b in 
                 let id = uid_of x in
                 let x = Bindlib.new_var (mk_free Zero) (name_of x) in 
                 let f = term_to_lterm f ((id,(x,Zero))::ctxt) in
                 let b = unbox (bind_var x (box_lterm (f,Zero))) in
                 let t = term_to_lterm t ctxt in
                 Prod ((t,Zero),b)
  |Appl (u,v) -> Appl ((term_to_lterm u ctxt,Zero),(term_to_lterm v ctxt,Zero),Succ Zero)
  |_ -> assert false

let rec term_to_lterm_witch_ctxt : term -> (int * ((lterm * layer) var*layer)) list -> lterm*(int * ((lterm * layer) var*layer)) list = fun t ctxt -> match t with 
  |Vari x -> begin try 
              let x,l = List.assoc (uid_of x) ctxt in Vari (x,l),ctxt
              with _ -> Vari ((Bindlib.new_var (mk_free Zero) (name_of x)),Zero),ctxt
            end
  |Type -> Type,ctxt
  |Kind -> Kind,ctxt
  |Symb s -> Symb s,ctxt
  |Prod (t,b) -> let x,f = unbind b in 
                 let id = uid_of x in
                 let x = Bindlib.new_var (mk_free Zero) (name_of x) in 
                 let f = fst (term_to_lterm_witch_ctxt f ((id,(x,Zero))::ctxt)) in
                 let b = unbox (bind_var x (box_lterm (f,Zero))) in
                 let t = fst(term_to_lterm_witch_ctxt t ctxt) in
                 Prod ((t,Zero),b),((id,(x,Zero))::ctxt)
  |Abst (t,b) -> let x,f = unbind b in 
                let id = uid_of x in
                let x = Bindlib.new_var (mk_free Zero) (name_of x) in 
                let f = fst (term_to_lterm_witch_ctxt f ((id,(x,Zero))::ctxt)) in
                let b = unbox (bind_var x (box_lterm (f,Zero))) in
                let t = fst(term_to_lterm_witch_ctxt t ctxt) in
                Abst ((t,Zero),b),((id,(x,Zero))::ctxt)
  |Appl (u,v) -> Appl ((term_to_lterm u ctxt,Zero),(term_to_lterm v ctxt,Zero),Succ Zero),ctxt
  |_ -> assert false

let rec check_layer : lterm -> (ltvar*layer) list -> bool = fun t ctxt -> match t with
  |Vari _ -> true
  |Type -> true
  |Kind -> true
  |Appl ((u,lu),(v,lv),lapp) -> ((eq lu Zero && eq lapp (Succ Zero)) || (sup_strict lu Zero && eq lu lapp)) && (check_layer u ctxt) && (check_layer v ctxt) && (sup lu lv)
  |Abst ((t,lt), b) -> let x,(u,lu) = unbind b in let lx = List.assoc x ctxt in sup lx lt && sup lx lu && check_layer t ctxt && check_layer u ctxt
  |Prod ((t,lt), b) -> let x,(u,lu) = unbind b in let lx = List.assoc x ctxt in sup lx lt && sup lx lu && check_layer t ctxt && check_layer u ctxt
  |_ -> false

let rec transform_ctxt : (int * ((lterm * layer) var*layer)) list -> (ltvar*layer) list = fun l -> match l with
  |(_,t)::q -> t::(transform_ctxt q)
  |[] -> []

let test : term -> bool = fun t -> let t,ctxt = term_to_lterm_witch_ctxt t [] in check_layer t (transform_ctxt ctxt)