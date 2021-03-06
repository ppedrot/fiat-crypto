
Require Import coqutil.Word.Interface.
Require Import Rewriter.Language.Wf.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.Bedrock.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.

Import API.Compilers.
Import Language.Wf.Compilers.

(** This file contains a record that contains a fully computed bedrock2
translation of a function, as well as all information about the computed term
that is necessary to prove the preconditions of translate_func. This way,
computation of the full term is separated from the rest of the proofs, which has
performance benefits. **)

Local Notation make_bedrock_func :=
  (@make_bedrock_func _ default_inname_gen default_outname_gen).

Record reified_op {p t}
       {name : String.string}
       {op : operation t}
       {start : ErrorT.ErrorT Pipeline.ErrorMessage
                              (API.Expr t)} :=
  { res : API.Expr t;
    computed_bedrock_func : bedrock_func;
    computed_bedrock_func_eq :
      computed_bedrock_func = make_bedrock_func name op res;
    reified_eq : start = ErrorT.Success res;
    reified_Wf3 : expr.Wf3 res;
    reified_valid : Func.valid_func (p:=p) (res (fun _ => unit));
  }.
Global Arguments reified_op {p t} name op start.

Ltac prove_reified_op :=
  lazymatch goal with |- reified_op _ _ _ => idtac end;
  econstructor;
  (* important to compute the function body first, before solving other
     subgoals *)
  lazymatch goal with
  | |- ?start = ErrorT.Success _ =>
    vm_compute; reflexivity
  | |- Func.valid_func _ => eapply valid_func_bool_iff
  | _ => idtac
  end;
  [ match goal with
    | |- _ = make_bedrock_func _ _ _ =>
      vm_compute; reflexivity end | .. ];
  match goal with
  | |- expr.Wf3 _ => abstract (prove_Wf3 ())
  | |- valid_func_bool ?x = true =>
    abstract vm_cast_no_check (eq_refl true)
  end.
Ltac make_reified_op p name op start :=
  assert (@reified_op p _ name op start) by prove_reified_op.
