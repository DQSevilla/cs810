(**
 * Type variable substitution interface
 * @author David Sevilla
 *)

(** Maps unique type variable strings to type expresions *)
type subst = (string,Ast.texpr) Hashtbl.t

(** Returns an empty substitution *)
val create : unit -> subst

(** Adds or replaces a type variable replacement *)
val extend : subst -> string -> Ast.texpr -> unit

(** Removes a type variable replacement *)
val remove : subst -> string -> unit

(** Attempts to find a type variable replacement *)
val lookup : subst -> string -> Ast.texpr option

(** Apply a subtitution to a type expression *)
val apply_to_texpr : subst -> Ast.texpr -> Ast.texpr

(** Apply a substitution to an expression to try and
 * decorate "lambda" types such as proc and letrec *)
val apply_to_expr : subst -> Ast.expr -> Ast.expr

(** Apply a substitution to a typing context *)
val apply_to_env : subst -> subst -> unit

(** Print a typing context or substitution *)
val string_of_subs : subst -> string

(** Return the domain of a subtitution as a list *)
val domain : subst -> string list

(** Compose a list of substitutions into one *)
val join : subst list -> subst

(** Get a list of unification goals for verifying the
 * pairwise compatability of a list of typing contexts *)
val compat : subst list -> (Ast.texpr*Ast.texpr) list

