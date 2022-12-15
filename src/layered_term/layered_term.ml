type layer =
|Zero
|Succ : layer -> layer
|Plus : layer*layer -> layer
|Var of string

type lterm =
|Vari of var
|MVari of var
|Type of layer 
|Kind of layer
|Appl of lterm*lterm*layer
|Abst of var*lterm*lterm*layer (**Abst("x",t,u) = Abst x : t.u*)
|Prod of var*lterm*lterm*layer
|Symb of string*(lterm list)*layer

and var = 
|Var of string*layer
|None (**used to check equality of symbols*)

type rules =
{
  lhs : lterm;
  rhs : lterm
}

let rec normal_form : layer -> layer = fun l -> match l with
|Plus(Zero,b) -> normal_form b
|Plus(a,Zero) -> normal_form a
|Plus(Succ a,b) -> Succ (normal_form (Plus(normal_form a,normal_form b)))
|Plus(a,Succ b) -> Succ (normal_form (Plus (normal_form a,normal_form b)))
|Plus(Var _,Var _) as t -> t
|Plus(Var _ as t, b) as l -> if b<>(normal_form b) then normal_form (Plus(t,normal_form b)) else l
|Plus(a,(Var _ as t)) as l -> if a <>normal_form a then normal_form (Plus(normal_form a, t)) else l
|Plus(a,b) as l -> if normal_form a <> a || normal_form b <> b then normal_form(Plus(normal_form a,normal_form b)) else l
|Succ(a) -> Succ(normal_form a)
|Var _ as t -> t
|Zero -> Zero

let rec sup : layer -> layer -> bool = fun l1 l2 -> match (normal_form l1,normal_form l2) with
|Zero,Zero -> true
|Succ a, Succ b -> sup a b
|Succ _, Zero -> true
|Zero, Succ _ -> false 
|_ -> failwith "comparaison de layer avec variables"
let inf : layer -> layer -> bool = fun l1 l2 -> sup l2 l1
let equal : layer -> layer -> bool = fun l1 l2 -> sup l1 l2 && inf l1 l2
let sup_strict : layer -> layer -> bool = fun l1 l2 -> sup l1 l2 && not (equal l1 l2)
let inf_strict : layer -> layer -> bool = fun l1 l2 -> inf l1 l2 && not (equal l1 l2)


let rec in_list : 'a -> 'a list -> bool = fun a l -> match l with
|t::q -> if t=a then true else in_list a q
|[] -> false

let test_doublons : 'a list -> 'a list = fun l -> 
  let rec aux acc seen = function
  |[] -> seen
  |t::q -> if in_list t acc && not (in_list t seen) then aux acc (t::seen) q else aux (t::acc) seen q
in aux [] [] l

let name_of : var -> string = fun x -> match x with
  |Var(s,_) -> s
  |_ -> failwith "You tried to get the name of a None variable"

(**Tester la non linéarité d'un côté d'une règle*)
let non_linear : lterm -> bool*lterm list = fun t ->
  let rec build_vars_list : lterm -> lterm list = fun t -> match t with
  |Vari x -> [Vari x]
  |MVari x -> [MVari x]
  |Type _ -> []
  |Kind _ -> []
  |Appl (u,v,_) -> (build_vars_list u)@(build_vars_list v)
  |Abst (_,t,u,_) -> (build_vars_list t)@(build_vars_list u)
  |Prod(_,t,u,_) -> (build_vars_list t)@(build_vars_list u)
  |Symb (_,l,_) -> extract_vars l
  and extract_vars : lterm list -> lterm list = fun l -> match l with
  |[] -> []
  |t::q -> let vars = build_vars_list t in vars@(extract_vars q)
in let vars_list = build_vars_list t in let l = test_doublons vars_list in (List.length l > 0),l

let suppr_doublons : 'a list -> 'a list = fun l ->
  let rec aux seen = function
  |[] -> seen
  |t::q -> if in_list t seen then aux seen q else aux (t::seen) q
in aux [] l

let non_left_linear_rule : rules -> bool*lterm list = fun r -> non_linear r.lhs
let non_right_linear_rule : rules -> bool*lterm list = fun r -> non_linear r.rhs
let non_linear_rule : rules -> bool*lterm list = fun r -> let bl,ll = non_left_linear_rule r and br,lr = non_right_linear_rule r in bl||br, suppr_doublons (ll@lr)

let equality_of_vars : var -> var -> bool = fun x y -> match x,y with
|Var (s,_), Var (s',_) -> s=s'
|_ -> failwith "Usage of None var outside of Sym equality checking"

(**equality without layers,return the list of equivalence of variables and meta_variables (just for the first term so need to apply rules first)*)
let equality_of_terms : lterm -> lterm -> bool*(lterm*lterm) list = fun t1 t2 -> 
  let rec aux : lterm -> lterm -> (lterm*lterm) list -> bool*(lterm*lterm) list = fun t1 t2 mapping -> match t1,t2 with
    |Vari a as x, (Vari b as y) -> if equality_of_vars a b then true,mapping else begin try let y' = List.assoc x mapping in aux y y' mapping with _ -> true,((x,y)::mapping) end
    |MVari _ as x, t -> begin try let t' = List.assoc x mapping in aux t' t mapping with |_ -> true,((x,t)::mapping) end
    |Kind _, Kind _ -> true,mapping
    |Type _, Type _ -> true,mapping
    |Appl (u,v,_), Appl (u',v',_) -> let b,m = aux u u' mapping in let b',m' = aux v v' m in (b&&b',m')
    |Abst (x,t,u,_), Abst (x',t',u',_) -> let b,m = aux t t' ((Vari x,Vari x')::mapping) in let b',m' = aux u u' m in (b&&b',m')
    |Prod (x,t,u,_), Prod (x',t',u',_) -> let b,m = aux t t' ((Vari x,Vari x')::mapping) in let b',m' = aux u u' m in (b&&b',m')
    |Symb (s,l,_), Symb (s',l',_) -> let m = (List.fold_left2 (fun mapping t1 t2 -> let b,m = (aux t1 t2 mapping) in if b then m else [Vari None,Vari None]) mapping l l') in (not (in_list (Vari None,Vari None) m) && s=s'),m
    |_ -> false,mapping
in (aux t1 t2 [])

(**check if a rule apply to a term return the value of all the metavariables*)
let rec rule_application : rules -> lterm -> bool*(lterm*lterm) list = fun r t -> 
  let b,l = (equality_of_terms r.lhs t) in if b then true,l else begin match t with
  |Appl (u,v,_) -> let (bu,lu),(bv,lv) = (rule_application r u),(rule_application r v) in bu||bv,lu@lv
  |Abst (_,t,u,_) -> let (bt,lt),(bu,lu) = (rule_application r t),(rule_application r u) in bt||bu,lt@lu
  |Prod (_,t,u,_) -> let (bt,lt),(bu,lu) = (rule_application r t),(rule_application r u) in bt||bu,lt@lu
  |Symb (_,l,_) -> let l = List.map (rule_application r) l in List.fold_left (fun (b1,l1) (b2,l2) -> b1||b2,l1@l2) (false,[]) l
  |_ -> false,[]
  end 

let rules_application : rules list -> lterm -> bool*(lterm*lterm) list = fun rl t -> 
  List.fold_left (fun (b1,l1) (b2,l2) -> b1||b2,l1@l2) (false,[]) (List.map (fun r -> rule_application r t) rl)

let rec filter_assoc : ('a*'b) list -> 'a list -> 'b list = fun l1 l2 -> match l1 with
  |[] -> []
  |(a,b)::q -> if in_list a l2 then b::(filter_assoc q l2) else filter_assoc q l2

(**return a list of the instanciation of non linear rule applicable*)
let non_linear_rule_application : rules -> lterm -> bool*(lterm) list = fun r t ->
  let b,non_linear_var_list = non_linear_rule r in
  if b then
    let b,l = rule_application r t in
    if b then 
      let values_of_metavar = filter_assoc l non_linear_var_list in 
      b,values_of_metavar
    else
      false,[]
  else 
    false,[]

let non_linear_rules_application : rules list -> lterm -> bool*(lterm list) = fun lr t ->
  let l = List.map (fun r -> non_linear_rule_application r t) lr in
  List.fold_left (fun (b1,l1) (b2,l2) -> b1||b2,l1@l2) (List.hd l) (List.tl l)

let get_layer : lterm -> layer = function
|Vari (Var (_,l)) -> l
|MVari (Var (_,l)) -> l
|Type l -> l
|Kind l -> l
|Appl (_,_,l) -> l
|Abst (_,_,_,l) -> l
|Prod (_,_,_,l) -> l
|Symb (_,_,l) -> l
|Vari (None) -> failwith "You tried to get the layer of a None variable"
|MVari (None) -> failwith "You tried to get the layer of a None variable"

let rec get_subterms_layers : lterm -> layer list = function
|Vari (Var (_,l)) -> [l]
|MVari (Var (_,l)) -> [l]
|Type l -> [l]
|Kind l -> [l]
|Appl (u,v,l) -> l::((get_subterms_layers u)@(get_subterms_layers v))
|Abst (_,t,u,l) -> l::((get_subterms_layers t)@(get_subterms_layers u))
|Prod (_,t,u,l) -> l::((get_subterms_layers t)@(get_subterms_layers u))
|Symb (_,args,l) -> l::(List.fold_left (fun l1 l2 -> l1@l2) [] (List.map (get_subterms_layers) args))
|Vari (None) -> failwith "You tried to get the layer of a None variablesubterm"
|MVari (None) -> failwith "You tried to get the layer of a None variable subterm"

let get_subterms_layers : lterm -> layer list = fun t -> test_doublons (get_subterms_layers t)

let rec check_layering : lterm -> bool = function
|Appl (u,v,l) -> let lu = get_layer u in let lv = get_layer v in 
                  let wl = if equal lu Zero then equal lv Zero && equal l Zero else equal lu l && inf lv lu in
                  wl && check_layering u && check_layering v
|Abst (x,t,u,l) -> let lx = get_layer (Vari x) in let lt = get_layer t in let lu = get_layer u in
                    equal lx l && inf lt lx && inf lu lx && check_layering t && check_layering u 
|Prod (x,t,u,l) -> let lx = get_layer (Vari x) in let lt = get_layer t in let lu = get_layer u in
                    equal lx l && inf lt lx && inf lu lx && check_layering t && check_layering u 
|Symb (_,_,l) as t -> List.fold_left (fun a b -> a && b) true (List.map (fun subtermlayer -> inf subtermlayer l) (get_subterms_layers t))
|_ -> true 

let check_non_linearity_layer : lterm -> rules list -> bool = fun t rl->
  let b,non_linear_vars = non_linear_rules_application rl t in
  if b then 
    let non_linear_layer = List.fold_left (fun a b -> a && b) true (List.map (fun st -> inf (Succ(get_layer st)) (get_layer t)) non_linear_vars) in
    non_linear_layer
  else 
    true

(**Test section*)
let x = Var ("x",Zero)
let y = Var ("y", Succ Zero)
let id = Abst (x,Type Zero,Vari x,Zero)
let id' = Abst (y,Type Zero,Vari y,Succ Zero)
let lhs = Symb("MAX",[MVari(Var("X",Zero));MVari(Var("X",Zero))],Zero)
let rhs = MVari(Var("X",Zero))
let rule = {lhs=lhs; rhs=rhs}
let t = Symb("MAX",[id;id],Succ(Zero))
let t' = Symb("MAX",[id';id'],Succ(Zero))