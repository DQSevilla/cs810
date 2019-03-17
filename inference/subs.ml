open Ast

type subst = (string,Ast.texpr) Hashtbl.t

let create () =
  Hashtbl.create 10

let extend sub key texp =
  Hashtbl.replace sub key texp

let remove sub key =
  Hashtbl.remove sub key

let lookup sub key =
  Hashtbl.find_opt sub key

let rec apply_to_texpr sub = function
  | VarType str ->
      (match lookup sub str with
      | Some t -> t
      | None -> VarType str)
  | FuncType (s, t) ->
      FuncType (apply_to_texpr sub s, apply_to_texpr sub t)
  | RefType t -> RefType (apply_to_texpr sub t)
  | other -> other

let rec apply_to_expr sub = function
  | Add (e1, e2) -> Add (apply_to_expr sub e1, apply_to_expr sub e2)
  | Sub (e1, e2) -> Sub (apply_to_expr sub e1, apply_to_expr sub e2)
  | Mul (e1, e2) -> Mul (apply_to_expr sub e1, apply_to_expr sub e2)
  | Div (e1, e2) -> Div (apply_to_expr sub e1, apply_to_expr sub e2)
  | IsZero (e) -> IsZero (apply_to_expr sub e)
  | NewRef (e) -> NewRef (apply_to_expr sub e)
  | DeRef (e) -> DeRef (apply_to_expr sub e)
  | SetRef (e1, e2) -> SetRef (apply_to_expr sub e1, apply_to_expr sub e2)
  | Let (str, def, body) ->
      Let (str, apply_to_expr sub def, apply_to_expr sub body)
  | Proc (spar, tpar, body) ->
      Proc (spar, apply_to_texpr sub tpar, apply_to_expr sub body)
  | ProcUntyped (spar, e) ->
      (match lookup sub spar with
      | Some t -> Proc (spar, t, apply_to_expr sub e)
      | None -> ProcUntyped (spar, apply_to_expr sub e))
  | Letrec (tfun, sfun, spar, tpar, def, body) ->
      Letrec (apply_to_texpr sub tfun,
              sfun, spar,
              apply_to_texpr sub tpar,
              apply_to_expr sub def,
              apply_to_expr sub body)
  | LetrecUntyped (sfun, spar, def, body) ->
      (match lookup sub sfun, lookup sub spar with
      | Some tfun, Some tpar ->
          Letrec (tfun, sfun, spar, tpar,
                  apply_to_expr sub def,
                  apply_to_expr sub body)
      | _, _ ->
          LetrecUntyped (sfun, spar,
                         apply_to_expr sub def,
                         apply_to_expr sub body))
  | App (f, a) -> App (apply_to_expr sub f, apply_to_expr sub a)
  | ITE (eif, ethen, eelse) ->
      ITE (apply_to_expr sub eif,
           apply_to_expr sub ethen,
           apply_to_expr sub eelse)
  | BeginEnd (elist) -> BeginEnd (List.map (apply_to_expr sub) elist)
  | other -> other

let apply_to_env sub gamma =
  Hashtbl.iter (fun key t -> extend gamma key (apply_to_texpr sub t)) gamma

let string_of_subs sub =
  let fmt = fun k t s -> s ^ k ^ ":=" ^ string_of_texpr t ^ "," in
  match Hashtbl.fold fmt sub "" with "" -> "empty" | str -> str

let domain sub =
  Hashtbl.fold (fun k t s -> k :: s) sub []

let rec join = function
  | s1 :: (s2 :: _ as next) ->
      Hashtbl.iter (fun key t1 ->
        match lookup s2 key with
        | None -> extend s2 key t1
        | Some t2 -> extend s2 key (apply_to_texpr s1 t2)) s1;
      join next
  | [s] -> s
  | [] -> create ()

(**
 * Helper utility for finding typing context compatability goals
 *)
let rec compat (l:subst list) :(Ast.texpr*Ast.texpr)list =
  let rec pairwise gamma = function
    | [] -> []
    | table :: rest ->
        (Hashtbl.fold (fun k t s ->
          match lookup gamma k with
          | Some u -> (t, u) :: s
          | _ -> s
        ) table []) @ (pairwise gamma rest) in
  match l with
  | [] -> []
  | gamma :: rest -> (pairwise gamma rest) @ (compat rest)

