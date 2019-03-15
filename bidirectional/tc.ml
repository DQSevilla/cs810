(**
 * David Sevilla, Noah Goldstein
 * We pledge our honor that we have abided by the Stevens Honor System
 *)

open Bindlib
open Ast

type 'a error = OK of 'a | Error of string

module Ctx = Map.Make(String)

let rec synthesize : texpr Ctx.t -> term -> texpr error = fun gamma m ->
  match m with
  | CstTrue | CstFalse -> OK BoolType
  | Var (x) ->
      (match Ctx.find_opt (name_of x) gamma with
      | Some s -> OK s
      | None -> Error ("type of " ^ name_of x ^ " not in typing context"))
  | App (func, body) ->
      (match synthesize gamma func with
      | OK FuncType (s, t) ->
          (match check gamma body s with
          | OK z when z=s -> OK t
          | err -> err)
      | OK _ -> Error "cannot apply a non-function type"
      | err -> err)
  | TDecl (x, t) -> check gamma x t
  | _ -> Error "type synthesis failed"
and check : texpr Ctx.t -> term -> texpr -> texpr error = fun gamma m sigma ->
  match m with
  | Abs (f) ->
      let (x, body) = unbind f in
      (match sigma with
      | FuncType (s, t) ->
          (match check (Ctx.add (name_of x) s gamma) body t with
          | OK tau when tau=t -> OK (FuncType (s, t))
          | OK _ -> Error "mismatched function range"
          | err -> err)
      | _ -> Error "expected function, got bool")
  | ITE (tcond, tthen, telse) ->
      (match check gamma tcond BoolType with
      | OK _ ->
          (match check gamma tthen sigma with
          | OK _ ->
              (match check gamma telse sigma with
              | OK _ -> OK sigma
              | err -> err)
          | err -> err)
      | err -> err)
  | other ->
      (match synthesize gamma other with
      | OK tau when tau=sigma -> OK sigma
      | OK _ -> Error "checking failed"
      | err -> err)

let tc : term -> texpr error = synthesize Ctx.empty
