open Ast
open Subs

type unif_result = UOk of Subs.subst | UError of texpr*texpr

(* Uses the Martelli-Montanari Algorithm (mma) *)
let mgu goals =
  let rec mma sublist = function
    | [] -> UOk (join sublist)
    | (VarType str1, VarType str2) :: goals ->
        let sub = create () in
        let high, low = if str1 > str2 then str2, str1 else str1, str2 in
        extend sub low (VarType high);
        mma (sub :: sublist) (List.map (fun (t1, t2) ->
          apply_to_texpr sub t1, apply_to_texpr sub t2) goals)
    | (VarType str, other) :: goals
    | (other, VarType str) :: goals ->
        if SetStr.mem str (fv_of_type other)
        then UError (VarType str, other)
        else
          let sub = create () in
          extend sub str other;
          mma (sub :: sublist) (List.map (fun (t1, t2) ->
            apply_to_texpr sub t1, apply_to_texpr sub t2) goals)
    | (FuncType (s1, t1), FuncType (s2, t2)) :: goals ->
        mma sublist ((s1, s2) :: (t1, t2) :: goals)
    | (RefType s, RefType t) :: goals ->
        mma sublist ((s, t) :: goals)
    | (s, t) :: goals when s = t ->
        mma sublist goals
    | (s, t) :: _ -> UError (s, t)
  in mma [] goals

