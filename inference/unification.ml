open Ast

type unif_result = UOk of Subs.subst | UError of texpr*texpr

let mgu goals =
  let rec mma goals sub =
    match goals with
    | (FuncType (s1, t1), FuncType (s2, t2)) :: g ->
        mma ((s1, t1) :: (s2, t2) :: g) sub
    | (IntType, IntType) :: g
    | (BoolType, BoolType) :: g ->
        mma goals sub
    | (VarType s1, VarType s2) :: g when s1=s2 ->
        mma goals sub
    | (VarType str, other) :: g
    | (other, VarType str) :: g ->
        if SetStr.mem str (fv_of_type other)
        then UError (VarType str, other)
        else begin
          Subs.extend sub str other;
          mma (List.map (fun (t1, t2) ->
            (Subs.apply_to_texpr sub t1, Subs.apply_to_texpr sub t2)) goals) sub
        end
    | (s, t) :: goals ->
        UError(s, t)
    | [] ->
        UOk sub
  in mma goals (Subs.create ())

