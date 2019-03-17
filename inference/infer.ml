open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string


type typing_judgement = subst*expr*texpr


let fresh n  = "_V" ^ string_of_int n

let unify' goals (n, (gammas, exp, texp)) =
  match mgu goals with
  | UOk sub ->
        List.iter (apply_to_env sub) gammas;
        let gamma = join gammas in
        OK (n, (gamma, apply_to_expr sub exp, apply_to_texpr sub texp))
  | UError (t1, t2) ->
      Error ("cannot unify "^string_of_texpr t1^" and "^string_of_texpr t2)

(* TODO: Replace all _'s in the OK matches with stuff like eif with eif
 * and replace all e's with the appropriate constructors *)
let rec infer' (e:expr) (n:int): (int*typing_judgement) error =
  match e with
  | Unit ->
      OK (n, (create (), e, UnitType))
  | Int _ ->
      OK (n, (create (), e, IntType))
  | Var str ->
      let texp = VarType (fresh n) in
      let sub = create() in
      extend sub str texp;
      OK (n+1, (sub, e, texp))
  | Add (l, r)
  | Sub (l, r)
  | Mul (l, r)
  | Div (l, r) ->
      let op l r = function
        | Add (_, _) -> Add (l, r)
        | Sub (_, _) -> Sub (l, r)
        | Mul (_, _) -> Mul (l, r)
        | Div (_, _) -> Div (l, r)
        | other -> other
      in (match infer' l n with
      | OK (n, (lg, le, lt)) ->
          (match infer' r n with
          | OK (n, (rg, re, rt)) ->
              let g = [lg; rg] in
              let goals = [(lt, IntType); (rt, IntType)] @ (compat g) in
              unify' goals (n, (g, op l r e, IntType))
          | err -> err)
      | err -> err)
  | IsZero m ->
      (match infer' m n with
      | OK (n, (g, m, t))  ->
          unify' [(t, IntType)] (n, ([g], IsZero m, BoolType))
      | err -> err)
  | ITE (eif, ethen, eelse) ->
      (match infer' eif n with
      | OK (n, (gif, eif, tif)) ->
          (match infer' ethen n with
          | OK (n, (gthen, ethen, tthen)) ->
              (match infer' eelse n with
              | OK (n, (gelse, eelse, telse)) ->
                  let g = [gif; gthen; gelse] in
                  let goals = [(tif, BoolType); (tthen, telse)] @ (compat g) in
                  unify' goals (n, (g, ITE(eif, ethen, eelse), tthen))
              | err -> err)
          | err -> err)
      | err -> err)
  | App (f, a) ->
      (match infer' f n with
      | OK (n, (gf, f, tf)) ->
          (match infer' a n with
          | OK (n, (ga, a, ta)) ->
              let g = [ga; gf] in
              let t = VarType (fresh n) in
              let goals = [(tf, FuncType(ta, t))] @ (compat g) in
              unify' goals ((n+1), (g, App (f, a), t))
          | err -> err)
      | err -> err)
  | Proc (spar, tpar, body) ->
      failwith "hard"
  | ProcUntyped (pstr, body) ->
      (match infer' body n with
      | OK (n, (g, body, t)) ->
          (match lookup g pstr with
          | Some u ->
                remove g pstr;
                OK (n, (g, Proc (pstr, u, body), FuncType (u, t)))
          | None ->
              let u = VarType (fresh n) in
              OK ((n+1), (g, Proc (pstr, u, body), FuncType (u, t))))
      | err -> err)
  | Letrec (tfun, sfun, spar, tpar, def, body) ->
      failwith "hard"
  | LetrecUntyped (sfun, spar, def, body) ->
      failwith "hard"
  | Let (str, var, body) ->
      (match infer' var n with
      | OK (n, (vg, ve, vt)) ->
          failwith "ree"
      | err -> err)
  | BeginEnd (elist) ->
      failwith "hard"
  | NewRef (v) ->
      (match infer' v n with
      | OK (n, (g, v, t)) ->
          OK (n, (g, NewRef v, RefType t))
      | err -> err)
  | DeRef (r) ->
      (match infer' r n with
      | OK (n, (g, r, t)) ->
          let s = VarType (fresh n) in
          unify' [(t, RefType s)] ((n + 1), ([g], DeRef r, s))
      | err -> err)
  | SetRef (r, v) ->
      (match infer' r n with
      | OK (n, (gr, r, tr)) ->
          (match infer' v n with
          | OK (n, (gv, v, tv)) ->
              let g = [gr; gv] in
              let goals = [(tr, RefType tv)] @ (compat g) in
              unify' goals (n, (g, SetRef (r, v), UnitType))
          | err -> err)
      | err -> err)


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

