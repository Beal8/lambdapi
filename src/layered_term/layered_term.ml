type layer =
|Zero
|Succ : layer -> layer
|Plus : layer*layer -> layer
|LVar of string
|Max of layer list 

type equations =
|Sup of layer * layer
|SupStrict of layer * layer
|Eq of layer*layer

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

let rec in_list : ('a -> 'a -> bool) -> 'a -> 'a list -> bool = fun eq a l -> match l with
|t::q -> if eq t a then true else in_list eq a q
|[] -> false

let rec count : 'a -> 'a list -> int = fun a l -> match l with
|[] -> 0
|t::q -> if t = a then 1+(count a q) else count a q

let rec normal_form : layer -> layer = fun l -> match l with
|Plus(Zero,b) -> normal_form b
|Plus(a,Zero) -> normal_form a
|Plus(Succ a,b) -> Succ (normal_form (Plus(normal_form a,normal_form b)))
|Plus(a,Succ b) -> Succ (normal_form (Plus (normal_form a,normal_form b)))
|Plus(LVar _,LVar _) as t -> t
|Plus(LVar _ as t, b) as l -> if b<>(normal_form b) then normal_form (Plus(t,normal_form b)) else l
|Plus(a,(LVar _ as t)) as l -> if a <>normal_form a then normal_form (Plus(normal_form a, t)) else l
|Plus(a,b) as l -> if normal_form a <> a || normal_form b <> b then normal_form(Plus(normal_form a,normal_form b)) else l
|Succ(a) -> Succ(normal_form a)
|LVar _ as t -> t
|Zero -> Zero
|Max l -> Max (List.map normal_form l)

let normal_term_form : lterm -> lterm = fun t ->
  let rec aux : string list -> lterm -> string list*lterm = fun seen_names t -> match t with
  |Vari (Var(name,l)) -> if in_list (fun x y -> x=y) name seen_names then seen_names,Vari (Var(name^(string_of_int (count name seen_names)),l)) else name::seen_names,Vari(Var(name,l))
  |Abst (Var(name,l),t,u,la) -> let seen_names_t,t = aux seen_names t in
                                let var_name = name^(string_of_int (count name seen_names_t+1)) in
                                let seen_names_u,u = aux (name::seen_names_t) u in
                                seen_names_u,Abst (Var(var_name,l),t,u,la)
  |Prod (Var(name,l),t,u,la) -> let seen_names_t,t = aux seen_names t in
                                let var_name = name^(string_of_int (count name seen_names_t+1)) in
                                let seen_names_u,u = aux (name::seen_names_t) u in
                                seen_names_u,Prod (Var(var_name,l),t,u,la)  
  |Type _ as t -> seen_names,t
  |Kind _ as t -> seen_names,t
  |Symb(s,lt,l) -> let rec apply_aux_to_list : string list -> lterm list -> string list * lterm list = fun seen_names args -> match args with
                      |[] -> seen_names,[]
                      |t::q -> let seen_names_t,t = aux seen_names t in
                        let seen_names_q,lt = apply_aux_to_list seen_names_t q in
                        seen_names_q,t::lt
                    in let seen_names,args = apply_aux_to_list seen_names lt 
                  in seen_names,Symb(s,args,l)
  |_ -> failwith "Tried to put in normal form Vari None" in
  let _,t = aux [] t in t


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

let test_doublons : 'a list -> 'a list = fun l -> 
  let rec aux acc seen = function
  |[] -> seen
  |t::q -> if in_list (fun x y -> x=y) t acc && not (in_list (fun x y -> x=y) t seen) then aux acc (t::seen) q else aux (t::acc) seen q
in aux [] [] l

let name_of : var -> string = fun x -> match x with
  |Var(s,_) -> s
  |_ -> failwith "You tried to get the name of a None variable"

(**Tester la non linéarité d'un côté d'une règle*)
let non_linear : lterm -> bool*lterm list = fun t ->
  let rec build_vars_list : lterm -> lterm list = fun t -> match t with
  |Vari _ -> []
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
  |t::q -> if in_list (fun x y -> x=y) t seen then aux seen q else aux (t::seen) q
in aux [] l

let non_left_linear_rule : rules -> bool*lterm list = fun r -> non_linear r.lhs
let non_right_linear_rule : rules -> bool*lterm list = fun r -> non_linear r.rhs
let non_linear_rule : rules -> bool*lterm list = fun r -> let bl,ll = non_left_linear_rule r and br,lr = non_right_linear_rule r in bl||br, suppr_doublons (ll@lr)

let equality_of_vars : lterm -> lterm -> bool = fun x y -> match x,y with
|Vari(Var (s,_)), Vari(Var (s',_)) -> s=s'
|_ -> failwith "Usage of None var outside of Sym equality checking"

let rec reverse_assoc : ('a*'b) list -> 'b -> 'a = fun l elt -> match l with
  |[] -> failwith "Not found"
  |(a,b)::q -> if b=elt then a else reverse_assoc q elt

(**equality without layers,return the list of equivalence of variables and meta_variables (just for the first term so need to apply rules first)*)
let equality_of_terms : lterm -> lterm -> bool*(lterm*lterm) list = fun t1 t2 -> 
  let rec aux : lterm -> lterm -> (lterm*lterm) list -> bool*(lterm*lterm) list = fun t1 t2 mapping -> match t1,t2 with
    |Vari _ as x, (Vari _ as y) -> if equality_of_vars x y then true,mapping else begin try let y' = List.assoc x mapping in equality_of_vars y y',mapping with _ -> begin try let x' = reverse_assoc mapping y in equality_of_vars x' x,mapping with |_ -> true,((x,y)::mapping) end end
    |MVari _ as x, t -> begin try let t' = List.assoc x mapping in aux t' t ((x,t)::mapping) with |_ -> true,((x,t)::mapping) end
    |Kind _, Kind _ -> true,mapping
    |Type _, Type _ -> true,mapping
    |Appl (u,v,_), Appl (u',v',_) -> let b,m = aux u u' mapping in let b',m' = aux v v' m in (b&&b',m')
    |Abst (x,t,u,_), Abst (x',t',u',_) -> let b,m = aux t t' ((Vari x,Vari x')::mapping) in let b',m' = aux u u' m in (b&&b',m')
    |Prod (x,t,u,_), Prod (x',t',u',_) -> let b,m = aux t t' ((Vari x,Vari x')::mapping) in let b',m' = aux u u' m in (b&&b',m')
    |Symb (s,l,_), Symb (s',l',_) -> let m = (List.fold_left2 (fun mapping t1 t2 -> let b,m = (aux t1 t2 mapping) in if b then m else [Vari None,Vari None]) mapping l l') in (not (in_list (fun x y -> x=y) (Vari None,Vari None) m) && s=s'),m
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
  |(a,b)::q -> if in_list (fun x y -> x=y) a l2 then b::(filter_assoc q l2) else filter_assoc q l2

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

let max : layer list -> layer = fun ll ->
  let rec aux current_max = function
    |[] -> current_max
    |t::q -> if sup t current_max then aux t q else aux current_max q
in aux Zero ll

let rec get_abst_var : lterm -> var list = fun t -> match t with
|Vari _ -> []
|MVari _ -> []
|Appl (u,v,_) -> (get_abst_var u)@(get_abst_var v)
|Prod (x,t,u,_) -> x::((get_abst_var t)@(get_abst_var u))
|Abst (x,t,u,_) -> x::((get_abst_var t)@(get_abst_var u))
|Symb (_,lt,_) -> let var_list_list = List.map (fun t -> get_abst_var t) lt in
                  List.fold_left (fun l1 l2 -> l1@l2) [] var_list_list
|Type _ -> []
|Kind _ -> []

let rec equality_mod_layer : lterm -> lterm -> bool = fun t1 t2 -> match t1,t2 with
|Vari (Var (x,_)),Vari (Var (y,_)) -> x=y
|MVari (Var (x,_)), MVari (Var (y,_)) -> x=y
|Type _,Type _ -> true
|Kind _, Kind _ -> true
|Appl (u,v,_),Appl(u',v',_) -> equality_mod_layer u u' && equality_mod_layer v v'
|Prod (Var(x,_),t,u,_),Prod (Var(x',_),t',u',_) -> x=x' && equality_mod_layer t t' && equality_mod_layer u u'
|Abst (Var(x,_),t,u,_),Abst (Var(x',_),t',u',_) -> x=x' && equality_mod_layer t t' && equality_mod_layer u u'
|Symb (s,lt,_),Symb(s',lt',_) -> s=s' && List.fold_left2 (fun b t1 t2 -> b && equality_mod_layer t1 t2) true lt lt'
|_ -> false

let infer_layer : rules list -> lterm -> lterm = fun rl t ->
  let _,non_linear_vars = non_linear_rules_application rl t in
(***  let abst_vars = get_abst_var t in*)
  let rec aux : (string*layer) list -> lterm -> lterm = fun layered_vars t ->
    match t with
    |Vari (Var (name, _)) -> let lx = begin try List.assoc name layered_vars with _ -> Zero end in
                                  Vari (Var (name, lx))
    |Type _ -> Type Zero
    |Kind _ -> Kind Zero
    |Appl (u,v,_) -> let layered_u = aux layered_vars u in
                      let layered_v = aux layered_vars v in 
                      Appl (layered_u,layered_v,max [get_layer layered_u; Succ Zero])
    |Abst (Var (s,_),t,u,_) -> let layered_t = aux layered_vars t in
                                let lt = get_layer layered_t in
                                Abst (Var (s,lt),layered_t,aux ((s,lt)::layered_vars) u, lt)
    |Prod (Var (s,_),t,u,_) -> let layered_t = aux layered_vars t in
    let lt = get_layer layered_t in
    Prod (Var (s,lt),layered_t,aux ((s,lt)::layered_vars) u, lt)
    |Symb(s,args,_) -> let layered_args = List.map (fun arg -> aux layered_vars arg) args in
                        Symb(s,layered_args, max(List.map (fun arg -> if in_list (fun x y -> x=y) arg non_linear_vars then Succ (get_layer arg) else get_layer arg) layered_args))
    |_ -> failwith "None variable found"
  in aux [] t

let generate_equations : rules list -> lterm -> (equations list)*lterm = fun rl t ->
  let _,non_linear_vars = non_linear_rules_application rl t in
  let rec aux : int -> (string*layer) list -> lterm -> equations list*lterm*int = fun counter layered_vars t ->
    match t with 
    |Vari (Var (name,_)) -> let lx = begin try List.assoc name layered_vars with _ -> Zero end in 
      [],Vari(Var(name,lx)),counter 
    |Type _ -> [],Type Zero,counter
    |Kind _ -> [],Kind Zero,counter
    |Appl (u,v,_) -> let equations_u,layered_u,counter = aux counter layered_vars u in
                      let equations_v,layered_v,counter = aux counter layered_vars v in
                      (Sup (get_layer layered_u,get_layer layered_v))::(equations_u@equations_v),Appl (layered_u,layered_v,Max([get_layer layered_u; Succ Zero])),counter
    |Abst (Var (s,_),t,u,_) -> let equations_t,layered_t,counter = aux counter layered_vars t in
                                let varlayer = LVar ("x"^(string_of_int counter)) in
                                let layered_vars = (s,varlayer)::layered_vars in
                                let counter = counter + 1 in
                                let equations_u,layered_u,counter = aux counter layered_vars u in
                                [Sup(varlayer,Max([get_layer layered_u;get_layer layered_t;Succ Zero]))]@(equations_t@equations_u),Abst (Var (s,varlayer),layered_t,layered_u,varlayer),counter
    |Prod (Var (s,_),t,u,_) -> let equations_t,layered_t,counter = aux counter layered_vars t in
                                let varlayer = LVar ("x"^(string_of_int counter)) in
                                let layered_vars = (s,varlayer)::layered_vars in
                                let counter = counter + 1 in
                                let equations_u,layered_u,counter = aux counter layered_vars u in
                                Sup(varlayer,Max([get_layer layered_u;get_layer layered_t;Succ Zero]))::(equations_t@equations_u),Prod (Var (s,varlayer),layered_t,layered_u,varlayer),counter
    |Symb (s,args,_) -> let rec apply_aux_to_list : int -> lterm list -> equations list*lterm list*int = fun counter t -> match t with
                            |[] -> [],[],0
                            |t::q -> let eqt,lt,counter = aux counter layered_vars t in 
                                      let eq,llt,counter = apply_aux_to_list counter q in
                                      eqt@eq,lt::llt,counter
                          in let eq,layered_args,counter = apply_aux_to_list counter args  
                        in eq,Symb(s,layered_args,Max(List.map (fun arg -> if in_list (equality_mod_layer) arg non_linear_vars then Succ (get_layer arg) else get_layer arg) layered_args)),counter
    |_ -> failwith "You tried to calculate layer of a None Variable"
  in let eq,lt,_ = aux 0 [] t in
  eq,lt
                                

    

(**Test section*)
let x = Var ("x",Zero)
let y = Var ("y", Succ Zero)

let z = Var ("z", Zero)
let id = Abst (x,Type Zero,Vari x,Zero)
let id' = Abst (y,Type Zero,Vari z,Succ Zero)
let lhs = Symb("MAX",[MVari(Var("X",Zero));MVari(Var("X",Zero))],Zero)
let rhs = MVari(Var("X",Zero))
let rule = {lhs=lhs; rhs=rhs}
let t = normal_term_form (Symb("MAX",[id;id],Succ(Zero)))

let t' = Abst(x,Type Zero, Symb("MAX",[Vari x;Vari x],Zero),(Zero))

let eq,t = generate_equations [rule] t