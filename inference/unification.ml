open Ast

type unif_result = UOk of Subs.subst | UError of texpr*texpr

(* TODO: Bug fix: Compose substitutions *)
let mgu goals =
  let rec mma sub = function
    | [] -> UOk sub
    | (FuncType (s1, t1), FuncType (s2, t2)) :: goals ->
        mma sub ((s1, s2) :: (t1, t2) :: goals)
    | (RefType s, RefType t) :: goals ->
        mma sub ((s, t) :: goals)
    | (VarType str1, VarType str2) :: goals ->
        let low, high = if str1 > str2 then str2, str1 else str1, str2
        in Subs.extend sub low (VarType high);
        mma sub (List.map (fun (t1, t2) ->
          (Subs.apply_to_texpr sub t1, Subs.apply_to_texpr sub t2)) goals)
    | (VarType str, other) :: goals
    | (other, VarType str) :: goals ->
        if SetStr.mem str (fv_of_type other)
        then UError (VarType str, other)
        else begin
          Subs.extend sub str other;
          mma sub (List.map (fun (t1, t2) ->
            (Subs.apply_to_texpr sub t1, Subs.apply_to_texpr sub t2)) goals)
        end
    | (s, t) :: goals when s = t ->
        mma sub goals
    | (s, t) :: _ -> UError (s, t)
  in mma (Subs.create ()) goals

