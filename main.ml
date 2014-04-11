
(* Damas-Milner type inference algorithm W *)

(* variable name *)
type vname = int
(* type variable name *)
type tvname = int

(* AST *)

(* literals *)
type lit = 
  | LInt of int
  | LBool of bool

(* expressions *)
type expr = 
  | EVar of vname
  | ELit of lit
  | EAbs of (vname*expr)
  | EApp of (expr*expr)
  | ELet of (vname*expr*expr)

(* TYPES *)

(* primitive types *)
type prim = PInt | PBool

(* monotypes *)
type mono = 
  | TVar of tvname (* type variables *)
  | TPrm of prim
  | TFun of (mono*mono) 
  | TError

(* set of tvnames *)
module S = Set.Make(struct type t = tvname let compare = compare end)

(* polytypes (type schemes) *)
type poly =
  | Mono of mono
  | Poly of (S.t * mono) (* universal quantification for the given set of type variables in the monotype *)

(* Free variables, substitution *)
(* Compute the set of free variables' names *)
let rec fv = function
  | Mono t ->
      ( match t with
        | TVar n -> S.singleton n
        | TFun (m1, m2) -> 
            S.union  (fv (Mono m2)) (fv (Mono m2))
        | TPrm _ 
        | TError -> S.empty
      ) 
  | Poly (tvns, m) -> S.diff (fv (Mono m)) tvns

module MT = Map.Make(struct type t = tvname let compare = compare end)
module MV = Map.Make(struct type t = vname let compare = compare end)

(* Substitution rule. Maps type variable names to monotypes *)
type subrule = mono MT.t
(* operations *)
let subrule_of_list ls = List.fold_left (fun sr (tvn,m) -> MT.add tvn m sr) MT.empty ls

(* Substitute free type variables with monotypes in a monotype *)
(* subrule -> tvname -> mono *)
let rec submono sr = function
  | TVar n -> if MT.mem n sr then MT.find n sr else TVar n
  | TFun (m1, m2) -> TFun (submono sr m1, submono sr m2)
  | x -> x

(* Substitute free type variables with monotypes in a polytype *)
(* subrule -> tvname -> poly *)
let rec subpoly sr = function
  | Mono m -> Mono (submono sr m)
  | Poly (tvns, m) -> 
      let sr2 = MT.filter (fun n m -> not (S.mem n tvns)) sr in
      Poly (tvns, submono sr2 m)

(* Substitution composition (s2 @@ s1) t = s2 (s1 t) *)      
let compose sr2 sr1 =
  MT.merge (fun n om2 om1 ->
    match om2, om1 with
    | _, Some m1 -> Some (submono sr2 m1)
    | Some m2, None -> Some m2
    | None, None -> None       
  ) sr1 sr2
let (@@) = compose

(* Environment *)      
(* Maps (variable name -> poly) *)
type env = poly MV.t 

(* operations with environments *)
let env_of_list ls = List.fold_left (fun env (vn,poly) -> MV.add vn poly env) MV.empty ls
let env_replace (vn,poly) env = MV.add vn poly env

(* Union of the free variables of all polytypes from the range of env *)
let fvenv env = MV.fold (fun _ p fvset -> S.union fvset (fv p)) env S.empty 

(* Substitute type variable binding (tvn:poly) with (tvn:sub(poly)) *)
let subenv sr env = MV.map (subpoly sr) env

(* Generalize monotype m by applying universal quantification for
   all free variables (fv(m) - fv(env))  *)
let generalize env m = Poly (S.diff (fv (Mono m)) (fvenv env), m)

let fresh_tvn = 
  let count = ref 0 in
  (fun () -> count := !count + 1; (!count - 1))

(* Polytupe to monotype, all quantified variables get replaced by fresh free type variables *)
let instantiate = function
  | Poly (tvns, m) ->
      let sr = S.fold (fun tvn acc -> MT.add tvn (TVar (fresh_tvn())) acc) tvns MT.empty in
      submono sr m
  | Mono m -> m


let rec occurs tvn = function
  | TVar n when n = tvn -> true
  | TFun (m1, m2) when occurs tvn m1 || occurs tvn m2 -> true
  | _ -> false

(* Unification of two monotypes - returns subrule *)
let rec unify m1 m2 = 
  match m1, m2 with
  | TPrm p1, TPrm p2 ->
      if p1 = p2 then Some MT.empty
      else None
  | TVar n1, _ when not (occurs n1 m2) -> Some (subrule_of_list [(n1, m2)])
  | _, TVar n2 when not (occurs n2 m1) -> Some (subrule_of_list [(n2, m1)])
  | TFun(m11,m12), TFun(m21,m22) ->
      (* first, try to unify the left sides *)
      ( match unify m11 m21 with
        | Some s1 ->
            ( (* if succeded, unify the right sides *)
              let s = (submono s1) in
              match unify (s m12) (s m22) with
              | Some s2 -> Some (s2 @@ s1)
              | _ -> None
            )
        | _ -> None
      )
  | _ -> None

(* Inference procedure - returns (subrule, monotype) *)
let rec algw env expr = 
  match expr with
  | EVar n -> 
      let m = if MV.mem n env then instantiate (MV.find n env) else TError in
      (MT.empty, m)
  | ELit lit -> 
      let litmono = match lit with 
        | LInt _ -> TPrm PInt 
        | LBool _ -> TPrm PBool in
      (MT.empty, litmono)
  | EAbs (vn, expr) ->
      let fresh_tv = TVar (fresh_tvn()) in
      let sr, mono = algw (env_replace (vn, Mono fresh_tv) env) expr in
      let abs_mono = TFun (fresh_tv, mono) in
      (sr, submono sr abs_mono)
  | EApp (e1, e2) ->
      let s1, m1 = algw env e1 in
      let s2, m2 = algw (subenv s1 env) e2 in
      let fresh_tv = TVar (fresh_tvn()) in
      ( match unify (submono s2 m1) (TFun (m2, fresh_tv)) with
        | Some s3 -> 
            let res_mono = submono s3 fresh_tv in
            (s3 @@ s2 @@ s1, res_mono)
        | _ -> (MT.empty, TError)
      )
  | ELet (n, e1, e2) ->
      let s1, m1 = algw env e1 in
      let s1env = subenv s1 env in
      let s2, m2 = algw (env_replace (n, generalize s1env m1) s1env) e2 in
      (s2 @@ s1, m2)

let infer env expr = 
  let sr, m = algw env expr in
  (sr, m)

open Printf  
let s_of_tvn x = 
  if x >= 0 && x < 26 then sprintf "%c" (Char.chr (97+x)) 
  else if x >= 0 && x < 26 + 26 then sprintf "%c" (Char.chr (65+x-26)) 
  else sprintf "(%i)" x

(* monotype to string *)
let rec s_of_m = function
  | TPrm PInt -> "int"
  | TPrm PBool -> "bool"
  | TVar n -> s_of_tvn n
  | TFun (m1, m2) -> "(" ^ s_of_m m1 ^ "->" ^ s_of_m m2 ^ ")"
  | TError -> "ERROR"

let test () =
  let env_empty = MV.empty in
  let e_fun_id = EAbs (0, EVar 0) in
  let e_fun_true = EAbs (0, (EAbs (1, EVar 0))) in
  let e_fun_false = EAbs (0, (EAbs (1, EVar 1))) in
  let e_true = ELit (LBool true) in
  let e_false = ELit (LBool false) in
  let e_1 = ELit (LInt 1) in
  let e_2 = ELit (LInt 2) in

  let s,m = infer env_empty (
      ELet (0, e_fun_id, 
        EApp (
          EApp (e_fun_false, EVar 0),
          EApp ( (EApp (EVar 0, EVar 0)),  e_false ) 
        )
      )
    ) in
  printf "%s\n" (s_of_m m)

let _ =
  test()
