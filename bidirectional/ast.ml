open Bindlib

type term =
  | CstTrue
  | CstFalse
  | Var of term var
  | App of term * term
  | Abs of (term, term) binder
  | ITE of term * term * term
  | TDecl of term * texpr
and texpr =
  | BoolType
  | FuncType of texpr * texpr

(* An example of how to traverse terms *)

let rec remove : 'a -> 'a list -> 'a list = fun x xs ->
  match xs with
  | [] -> []
  | y::xs when x=y -> remove x xs
  | y::xs -> y::remove x xs

let rec fv : term -> string list = fun t ->
  match t with
  | CstTrue | CstFalse -> []
  | Var(x) -> [name_of x]
  | Abs(f) ->
     let (x, t) = unbind f in
     remove (name_of x) (fv t)
  | App(t, u) ->
     (fv t) @ (fv u)
  | ITE(tc, tthen, telse) ->
     (fv tc) @ (fv tthen) @ (fv telse)
  | TDecl(t, ty) -> fv t

let _CstTrue : term box =
  box CstTrue
let _CstFalse : term box =
  box CstFalse
let _Var : term var -> term box =
  box_var
let _Abs : (term, term) binder box -> term box =
  box_apply (fun f -> Abs(f))
let _App : term box -> term box -> term box =
  box_apply2 (fun t u -> App(t, u))
let _ITE : term box -> term box -> term box -> term box =
  box_apply3 (fun t u v -> ITE(t, u, v))
let _TDecl : term box -> texpr box -> term box =
  box_apply2 (fun t u -> TDecl(t, u))

let rec lift_type : texpr -> texpr box = fun t ->
  match t with
  | BoolType -> box BoolType
  | FuncType(u,v) -> box_apply2 (fun u v -> FuncType(u,v))
                       (lift_type u) (lift_type v)

let rec lift_term : term -> term box = fun t ->
  match t with
  | CstTrue -> _CstTrue
  | CstFalse -> _CstFalse
  | Var(x) -> _Var x
  | Abs(f) -> _Abs (box_binder lift_term f)
  | App(t, u) -> _App (lift_term t) (lift_term u)
  | ITE(t, u, v) -> _ITE (lift_term t) (lift_term u) (lift_term v)
  | TDecl(t, ty) -> _TDecl (lift_term t) (lift_type ty)

let rec nf : term -> term = fun t ->
  match t with
  | CstTrue | CstFalse | Var(_) -> t
  | Abs(f) ->
     let (x, t) = unbind f in
     Abs(unbox (bind_var x (lift_term (nf t))))
  | App(t, u) ->
     begin
       match nf t with
       | Abs(f) -> nf (subst f u)
       | v      -> App(v, nf u)
     end
  | ITE(tc, tthen, telse) ->
     begin
       match nf tc with
       | CstTrue -> nf tthen
       | CstFalse -> nf telse
       | v -> ITE(v, nf tthen, nf telse)
     end
  | TDecl(t, _) -> nf t

let rec string_of_type : texpr -> string = function
  | BoolType -> "bool"
  | FuncType(s, t) -> "(" ^ string_of_type s ^ " -> " ^ string_of_type t ^ ")"

let rec string_of_term : term -> string = function
  | CstTrue -> "True"
  | CstFalse -> "False"
  | Var(x) -> name_of x
  | Abs(b) ->
     let (x, a) = unbind b
     in "(lam " ^ (name_of x) ^ "." ^ string_of_term a ^ ")"
  | App(t, u) ->
     "(" ^ string_of_term t ^ "  " ^ string_of_term u ^ ")"
  | ITE(t, u, v) ->
     "if " ^ string_of_term t ^ " then " ^ string_of_term u ^ " else "
     ^ string_of_term v
  | TDecl(t, ty) -> string_of_term t ^ " : " ^ string_of_type ty


(* Examples of building terms *)

let var_x : term var = new_var (fun x -> Var(x)) "x"
let var_f : term var = new_var (fun x -> Var(x)) "f"

(* (lam f.(lam x. f (f x))) *)
let ex1 : term box =
  _Abs (bind_var var_f (_Abs (bind_var var_x (_App (_Var var_f)
                                                (_App (_Var var_f) (_Var var_x))))))

let ex2 : term box =
  _App ex1 ex1

let ex3 : term box =
  _App ex1 (_Var var_x)

let ex4 : term =
  App(Var(var_x), Var(var_x))

let _t3 : term box =
  _Abs (bind_var var_f (_Abs (bind_var var_x (_App (_Var var_f)
                                                (_App (_Var var_x) (_Var var_x))))))

let t3 : term = unbox _t3


(* [parsedterm] is how we would normally encode terms without using
 * Bindlib.  This is used here to avoid issues during parsing.
 *
 * An issue arises when we try to parse strings of the form "lam x. M"
 * where "x" is not free in "M".  While parsing, we have to create a new
 * variable for "x" using Bindlib.new_var.  However, how must we handle the
 * occurences of "x" in "M"?
 *
 * Clearly we cannot create new variables and must reuse the one created
 * for "x".  This complicates matters, since we now have to keep track
 * of all variables we created (presumably using a mapping between strings
 * to terms of type [term var]), and figure out where to apply them.
 *
 * Rather than doing this process while parsing, we choose to delay it
 * and convert everything into an intermediate representation ([parsedterm]).
 * We can then translate this representation into an appropriate value of
 * type [term] in a relatively straightforward manner.
 *)

type parsedterm =
  | PCstTrue
  | PCstFalse
  | PVar of string
  | PAbs of string * parsedterm
  | PApp of parsedterm * parsedterm
  | PITE of parsedterm * parsedterm * parsedterm
  | PTDecl of parsedterm * texpr

let trans : parsedterm -> term =
  let rec trans : (string * term var) list -> parsedterm -> term box =
    fun env t ->
    match t with
    | PVar(x) -> (try _Var (List.assoc x env)
                  with Not_found -> _Var (new_var (fun x -> Var(x)) x))
    | PAbs(x,u) -> let v = new_var (fun x -> Var(x)) x in
                   _Abs (bind_var v (trans ((x,v)::env) u))
    | PApp(u,v) -> _App (trans env u) (trans env v)
    | PITE(u,v,w) -> _ITE (trans env u) (trans env v) (trans env w)
    | PTDecl(u,v) -> _TDecl (trans env u) (lift_type v)
    | PCstTrue -> _CstTrue
    | PCstFalse -> _CstFalse
  in fun t -> unbox (trans [] t)
