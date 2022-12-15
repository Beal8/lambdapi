open Common
open Core
open Syntax
open  Timed
open Lplib.Extra
module T = Term

(* TODO: factorise modules *)

module type BUILDER = sig
  val term: ?sig_st:Sig_state.t -> string -> T.term
  val create_symbole: ?ss:Sign.t -> string -> Term.term -> Sig_state.sig_state * Sign.t
end

module Lp : BUILDER = struct
let term: ?sig_st:Sig_state.t -> string -> Term.term = fun ?sig_st s ->
  let wrapped = Format.sprintf "compute %s;" s in
  let Pos.{elt=cmd;_} = Stream.next (Parser.parse_string "" wrapped) in
  let pt =
    match cmd with
    | P_query {elt=(P_query_normalize (te,_)); _} -> te
    | P_symbol {p_sym_typ = Some t;_} -> t
    | _ -> assert false
  in
  let sig_st = match sig_st with
  | Some ss -> ss
  | None ->
      let sign = Sig_state.create_sign ["unparse"] in
      Sig_state.of_sign sign
  in
  Scope.scope_term false sig_st [] pt

let create_symbole: ?ss:Sign.t -> string -> Term.term -> Sig_state.sig_state * Sign.t = fun ?ss name stype ->
  let ss = match ss with
    |Some ss -> ss
    |None -> Sig_state.create_sign []
  in
  let _ = Sign.add_symbol ss (Term.Public) (Term.Const) (Term.Eager) false (Pos.{elt=name; pos = None}) stype [] in
  let st = Sig_state.of_sign ss in
  let a = (!)(st.signature.sign_symbols) in
  let symblist = (StrMap.bindings a) in

  let rec aux st = function
    |[] -> st
    |symb::q -> aux (Sig_state.{in_scope = (StrMap.add (fst(symb)) (snd(symb)) st.in_scope);
                      signature = st.signature;
                      alias_path = st.alias_path;
                      path_alias = st.path_alias;
                      builtins = st.builtins;
                      notations = st.notations;
                      open_paths = st.open_paths
                               }) q in
  let st = aux st symblist in
  (st,ss)


end

(**module Dk : BUILDER = struct
let term: ?sig_st:Sig_state.t -> ?pb:T.problem -> string -> Term.term = fun ?sig_st ?pb s ->
  let wrapped = Format.sprintf "#EVAL %s." s in
  let Pos.{elt=cmd;_} = Stream.next (Parser.Dk.parse_string "" wrapped) in
  let pt =
    match cmd with
    | P_query {elt=(P_query_normalize (te,_)); _} -> te
    | _ -> assert false
  in
  let sig_st = match sig_st with
  | Some ss -> ss
  | None ->
      let sign = Sig_state.create_sign ["unparse"] in
      Sig_state.of_sign sign
  in
  let pb = match pb with Some pb -> pb | None -> Term.new_problem () in
  let m _ = None in
  Scope.scope_term false sig_st [] pb m m pt
   end*)
