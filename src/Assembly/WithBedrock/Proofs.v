From Coq Require Import Permutation.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import NArith.
From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.CastLemmas.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldMap.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.ListUtil.Filter.
Require Import Crypto.Util.ListUtil.Split.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.LandLorBounds.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RevertUntil.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ClearHead.
Require Import Crypto.Assembly.EquivalenceProofs.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.WithBedrock.SymbolicProofs.
Import Assembly.Symbolic.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope list_scope.

(* TODO: move to global settings *)
Local Set Keyed Unification.

Import Map.Interface Map.Separation. (* for coercions *)
Require Import bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import Rupicola.Lib.Tactics. (* for sepsimpl *)
Import LittleEndianList.
Import coqutil.Word.Interface.

Definition R_regs_preserved_v rn (m : Semantics.reg_state)
  := Z.land (Tuple.nth_default 0%Z rn m) (Z.ones 64).

Definition R_regs_preserved G d G' d' (m : Semantics.reg_state) rs rs'
  := forall rn idx, Symbolic.get_reg rs' rn = Some idx -> exists idx', Symbolic.get_reg rs rn = Some idx' /\ let v := R_regs_preserved_v (N.to_nat rn) m in eval_idx_Z G d idx' v -> eval_idx_Z G' d' idx v.

Lemma R_regs_preserved_set_reg G d G' d' rs rs' ri rm v
      (H : R_regs_preserved G d G' d' rm rs rs')
      (H_same : (ri < N.of_nat (List.length widest_registers))%N -> exists idx, Symbolic.get_reg rs ri = Some idx /\ let v' := R_regs_preserved_v (N.to_nat ri) rm in eval_idx_Z G d idx v' -> eval_idx_Z G' d' v v')
  : R_regs_preserved G d G' d' rm rs (Symbolic.set_reg rs' ri v).
Proof.
  cbv [R_regs_preserved] in *.
  intros rn idx; specialize (H rn).
  rewrite get_reg_set_reg_full; intro.
  vm_compute (length widest_registers) in *.
  repeat first [ progress break_innermost_match_hyps
               | progress inversion_option
               | progress subst
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress destruct_head'_ex
               | progress specialize_by_assumption
               | progress specialize_by lia
               | rewrite @Bool.andb_true_iff in *
               | rewrite @Bool.andb_false_iff in *
               | solve [ eauto ]
               | progress reflect_hyps
               | match goal with
                 | [ H : forall v, ?k = Some v -> _, H' : ?k = Some _ |- _ ]
                   => specialize (H _ H')
                 end ].
Timeout 5 Qed.
