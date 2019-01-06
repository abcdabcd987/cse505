Require Import List.
Require Import String.
Require Import ZArith.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Require Import Imp.ImpSyntax.
Require Import Imp.ImpCommon.

(*
 * In this file, you will finish writing the interpreter for Imp.
 * You should use the semantics in ImpEval.v as a guide.
 *)

Definition interp_op1
  (op : op1) (v : val) : option val :=
  match op, v with
  | Oneg, Vint i =>
      Some (Vint (Z.opp i))
  | Onot, Vbool b =>
      Some (Vbool (negb b))
  | _, _ =>
      None
  end.

(*
 * Problem 1 [20 points, ~30 LOC]: Complete the rest of interp_op2.
 * The semantics for this are in eval_binop in ImpEval.v.
 *
 * Once you have written this, uncomment the proof of eval_op2_interp_op2 in 
 * ImpInterpProof.v.
 *)
Definition interp_op2
  (op : op2) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | Oadd, Vint i1, Vint i2 =>
      Some (Vint (Z.add i1 i2))
  | Odiv, Vint i1, Vint i2 =>
      if Z.eq_dec i2 0 then
        None
      else
        Some (Vint (Z.div i1 i2))
  (* YOUR CODE HERE *)
  | _, _, _ =>
      None
  end.

Fixpoint interp_e (s : store) (h : heap)
  (e : expr) : option val :=
  match e with
  | Eval v => Some v
  | Evar x => lkup s x
  | Eop1 op e1 =>
      match interp_e s h e1 with
      | Some v1 => interp_op1 op v1
      | _ => None
      end
  | Eop2 op e1 e2 =>
      match interp_e s h e1, interp_e s h e2 with
      | Some v1, Some v2 => interp_op2 op v1 v2
      | _, _ => None
      end
  | Elen e1 =>
      match interp_e s h e1 with
      | Some (Vaddr a) =>
          match read h a with
          | Some (Vint l) => Some (Vint l)
          | _ => None
          end
      | Some (Vstr cs) =>
          Some (Vint (Z.of_nat (String.length cs)))
      | _ => None
      end
  | Eidx e1 e2 =>
      match interp_e s h e1, interp_e s h e2 with
      | Some (Vaddr a), Some (Vint i) =>
          match read h a with
          | Some (Vint l) =>
              if Z_le_dec 0 i then
                if Z_lt_dec i l then
                  read h (Z.succ (a + i))
                else
                  None
              else
                None
          | _ => None
          end
      | Some (Vstr cs), Some (Vint i) =>
          if Z_le_dec 0 i then
            match String.get (Z.to_nat i) cs with
            | Some c =>
                Some (Vstr (String c EmptyString))
            | None => None
            end
          else
            None
      | _, _ => None
      end
  end.

Fixpoint interps_e (s : store) (h : heap)
  (es : list expr) : option (list val) :=
  match es with
  | nil => Some nil
  | e :: t =>
      match interp_e s h e, interps_e s h t with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(*
 * Problem 2 [25 points, ~70 LOC]: Complete the rest of interp_s. 
 * The semantics for this are in eval_s in ImpEval.v.
 *
 * Hint: If you are lost, try walking through and understanding how one of the 
 * cases that is already filled in (say, Salloc) relates to the corresponding
 * constructors of eval_s (eval_alloc). Also, note that it is OK to have
 * a single case that corresponds to multiple different constructors of eval_s, 
 * much like the Scall case that is already filled in.
 *)
Fixpoint interp_s (fuel : nat) (env : env) (s : store) (h : heap)
  (p : stmt) : option (store * heap) :=
  match fuel with O => None | S n =>
    match p with  
    | Salloc x e1 e2 =>
        match interp_e s h e1, interp_e s h e2 with
        | Some (Vint i), Some v =>
            if Z_le_dec 0 i then
              Some (update s x (Vaddr (zlen h)), alloc h i v)
            else
              None
        | _, _ => None
        end
    | Swrite x e1 e2 =>
        match lkup s x
            , interp_e s h e1
            , interp_e s h e2 with
        | Some (Vaddr a), Some (Vint i), Some v =>
            match read h a with
            | Some (Vint l) =>
                if Z_le_dec 0 i then
                  if Z_lt_dec i l then
                    match write h (Z.succ (a + i)) v with
                    | Some h' => Some (s, h')
                    | None => None
                    end
                  else
                    None
                else
                  None
            | _ => None
            end
        | _, _, _ => None
        end
    | Scall x f es =>
        match interps_e s h es with
        | Some vs =>
            match locate env f with
            | Some (Func _ params body ret) =>
                match updates store_0 params vs with
                | Some sf =>
                    match interp_s n env sf h body with
                    | Some (s', h') =>
                        match interp_e s' h' ret with
                        | Some v' =>
                            Some (update s x v', h')
                        | None => None
                        end
                    | None =>
                        None
                    end
                | None =>
                    None
                end
            | None =>
                if extcall_args_ok f vs h then
                  let (v', h') := extcall f vs h in
                  Some (update s x v', h')
                else
                  None
            end
        | None => None
        end
    (* YOUR CODE HERE *)
    | _ => None
    end
  end.

Definition interp_p (fuel : nat) (p : prog) : option (heap * val) :=
  match p with
  | Prog funcs body ret =>
      match interp_s fuel funcs store_0 heap_0 body with
      | Some (s', h') =>
          match interp_e s' h' ret with
          | Some v' => Some (h', v')
          | None => None
          end
      | None => None
      end
  end.
