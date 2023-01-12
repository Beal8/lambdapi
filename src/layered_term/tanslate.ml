open Layered_term
open Core.Term

let rec translate : term -> lterm = function
  | Vari x -> Vari(Var (Bindlib.name_of x,Zero))
  | Type -> Type Zero
  | Kind -> Kind Zero
  | _ -> failwith ""