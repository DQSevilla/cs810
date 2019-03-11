open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string


type typing_judgement = subst*expr*texpr


let fresh n  = "_V" ^ string_of_int n

let unify goals (n, (gamma, exp, texp)) =
  match mgu goals with
  | UOk sub -> begin
      apply_to_env sub gamma;
      OK (n, (gamma, apply_to_expr sub exp, apply_to_texpr sub texp)) end
  | UError (t1, t2) ->
      Error ("cannot unify " ^ string_of_texpr t1 ^ " and " ^ string_of_texpr t2)


let rec infer' (e:expr) (n:int): (int*typing_judgement) error =
  match e with
  | Int _ ->
      OK (n, (create (), e, IntType))
  | Var str ->
      let texp = VarType (fresh n) in
      let sub = create() in
      begin
        extend sub str texp;
        OK (n+1, (sub, e, texp))
      end
  | Add (l, r)
  | Sub (l, r)
  | Mul (l, r)
  | Div (l, r) ->
      (match infer' l n with
      | OK (n, (lg, le, lt)) ->
          (match infer' r n with
          | OK (n, (rg, re, rt)) ->
              (* unify [(lt, IntType); (rt, IntType); compat(...)?] (n, ((union
               * lg rg), e, IntType*)
              Error "ree"
          | err -> err)
      | err -> err)
  | IsZero m ->
      (match infer' m n with
      | OK (n, (g, _, t))  ->
          unify [(t, IntType)] (n, (g, e, BoolType))
      | err -> err)
  | _ -> failwith "infer': undefined"


let string_of_typing_judgement (s, e, t) =
  "\027[36m "^string_of_subs s^"\027[31m |- \027[39m"^string_of_expr e
  ^": \027[32m "^string_of_texpr t


let infer_type (AProg e) =
  match infer' e 0 with
  | OK (_, tj) -> string_of_typing_judgement tj
  | Error s -> "Error! "^ s



let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast


(* Interpret an expression *)
let inf (e:string) : string =
  e |> parse |> infer_type

let test (n:int) : string =
  Examples.expr n |> parse |> infer_type
