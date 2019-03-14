open Ast

type unif_result = UOk of Subs.subst | UError of texpr*texpr

let mgu goals =
  let rec mma sub = function
    | [] -> UOk sub (* TODO: Need to join a bunch of subs? *)
    | (FuncType (s1, t1), FuncType (s2, t2)) :: goals ->
        mma sub ((s1, s2) :: (t1, t2) :: goals)
    | (VarType str1, VarType str2) :: goals when str1=str2 ->
        (* TODO: need to actually unify, how to pick?
         * could let it depend on my infer' *)
        mma sub goals
    | (RefType s, RefType t) :: goals ->
        mma sub ((s, t) :: goals)
    | (VarType str, other) :: goals
    | (other, VarType str) :: goals ->
        if SetStr.mem str (fv_of_type other)
        then UError (VarType str, other)
        else begin
          (* TODO: Cannot simply extend here or can we because we can assume no
           * vartype of the same str will appear in here? Do we need to
           * apply_env? *)
          Subs.extend sub str other;
          mma sub (List.map (fun (t1, t2) ->
            (Subs.apply_to_texpr sub t1, Subs.apply_to_texpr sub t2)) goals)
        end
    | (s, t) :: goals when s=t ->
        mma sub goals
    | (s, t) :: _ -> UError (s, t)
  in mma (Subs.create ()) goals

