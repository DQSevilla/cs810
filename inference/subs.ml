open Ast

type subst = (string,Ast.texpr) Hashtbl.t

let create (x:unit) =
  Hashtbl.create 1

(* Using this rather than add *)
let extend substitution key texp =
  Hashtbl.replace substitution key texp

let remove substitution key =
  Hashtbl.remove substitution key

let lookup substitution key =
  Hashtbl.find_opt substitution key

let rec apply_to_texpr sub = function
  | VarType str ->
      (match lookup sub str with
      | Some t -> t
      | None -> VarType str)
  | FuncType (s, t) ->
      FuncType (apply_to_texpr sub s, apply_to_texpr sub t)
  | RefType r -> RefType (apply_to_texpr sub r)
  | other -> other

let apply_to_expr sub = function
  | ProcUntyped (str, exp) ->
      (match lookup sub str with
      | Some t -> Proc (str, t, exp)
      | None -> failwith "substitution on proc failed")
  | LetrecUntyped (id, p, pexp, body) ->
      (match lookup sub id, lookup sub p with
      | Some s, Some t -> Letrec (s, id, p, t, pexp, body)
      | _, _ -> failwith "substitution on letrec failed")
  | other -> other

let apply_to_env sub gamma =
  Hashtbl.iter (fun key t ->
    match lookup gamma key with
    | Some s -> extend gamma key s
    | None -> ()) sub

let string_of_subs sub =
  match Hashtbl.length sub with
  | 0 -> "empty"
  | _ -> (Hashtbl.fold (fun k t s -> s^k^":="^(string_of_texpr t)^",") sub "")

let domain substitution =
  Hashtbl.fold (fun k t s -> k :: s) substitution []

let rec join = function
  | s1 :: (s2 :: rest as next) ->
      begin
        Hashtbl.iter (fun key t -> extend s2 key t) s1;
        join next
      end
  | [s] -> s
  | _ -> failwith "ree"

