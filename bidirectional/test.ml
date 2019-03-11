open Ast
open Lexer
open Lexing
open Printf
open OUnit

type tc_assert = Checks | Fails

(* Each example returns a string representing a term, the expected type,
 * the name of the test case, and whether the test should pass or fail.
 * Test cases that should fail have a default type of "bool" (which is
 * ignored in subsequent functions).
 *
 * You can add more examples to this function without having to change
 * any of the testing code below.
 *)
let examples : int -> (string * string * string * tc_assert) = function
  | 1  -> "true",
          "bool", "constant true", Checks

  | 2  -> "false",
          "bool", "constant false", Checks

  | 3  -> "(lam x. x : bool -> bool)",
          "bool -> bool", "bool identity", Checks

  | 4  -> "(lam x. lam y. x : bool -> bool -> bool)",
          "bool -> bool -> bool", "bool const", Checks

  | 5  -> "(lam f. lam x. (f x) : (bool -> bool) -> bool -> bool)",
          "(bool -> bool) -> bool -> bool", "app inside lam", Checks

  | 6  -> "(lam x. if x then false else true : bool -> bool)",
          "bool -> bool", "~ (not) function", Checks

  | 7  -> "((lam x. x : bool -> bool) true)",
          "bool", "identity applied to true", Checks

  | 8  -> "((lam f. (lam x. (f x)) : (bool -> bool) -> bool -> bool)
            (lam x. x))",
          "bool -> bool", "identity applied to identity", Checks

  | 9  -> "((lam x. if x then false else x : bool -> bool) true)",
          "bool", "not applied to true", Checks

  | 10 -> "((lam f. (lam x. (f (f x))) : (bool -> bool) -> bool -> bool)
            (lam x. x))",
          "bool -> bool", "double apply identity", Checks

  | 11 -> "(x : bool)",
          "bool", "unbound annotated variable", Fails

  | 12 -> "(if (x : bool) then (y : bool) else (z : bool))",
          "bool", "if with unbound variables", Fails

  | 13 -> "(lam x. if x then x else (lam x. x : bool -> bool) : bool -> bool)",
          "bool", "if with different branch types", Fails

  | 14 -> "(true false)",
          "bool", "true applied to false", Fails

  | n  -> failwith @@ "Expression " ^ string_of_int n ^ " not defined."


(* Parsing terms and types *)

exception SyntaxError

let parse pfun s =
  let print_position outx lexbuf =
    let pos = lexbuf.lex_curr_p in
    fprintf outx "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  in
  let lexbuf = from_string s in
  try pfun read lexbuf with
  | Parser.Error ->
     fprintf stderr "%a: syntax error\n" print_position lexbuf;
     raise SyntaxError

let parse_term = parse Parser.main
let parse_type = parse Parser.maintype


(* Testing
 *
 * [check_term] is a wrapper around your type-checking function.  It takes
 * a string, parses it, and then type-checks.  [get_type] parses a type
 * but returns a [texpr Tc.error] in order to make it easier to assert that
 * the synthesized type is equal to the expected type.
 *
 * [tests] is the test suite we will be working with.  ``make test'' should
 * run each test in this suite.
 *)
let check_term : string -> texpr Tc.error = fun s ->
  s |> parse_term |> Tc.tc

let get_type : string -> texpr Tc.error = fun s ->
  OK (s |> parse_type)

let is_error : texpr Tc.error -> bool = function
  | OK _ -> false
  | Error _ -> true

let make_single_test : int -> test = fun n ->
  match examples n with
  | (t, ty, name, Checks) ->
     name >:: (fun _ -> assert_equal (check_term t) (get_type ty))
  | (t, _, name, Fails) ->
     name >:: (fun f ->
      assert_bool ("Expected type checking to fail for  ("
                   ^ (string_of_term (parse_term t)) ^ ")")
                  (is_error (check_term t)))

let tests : test =
  let rec aux n = (make_single_test n) :: (try aux (n + 1) with _ -> [])
  in "Test suite -- bidirectional type checker" >::: aux 1

(* Comment out line below to not run the test suite *)
(* let _ = run_test_tt_main tests *)
