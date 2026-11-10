module

public import ArtinMatthews.GiantSignedEdgeIndices
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Every promotion is an actual injection into the old indexed memory.
The enumeration equivalence keeps retrieval order and survivor order separate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedPromotionFamilyEquiv {J : Type*} (k a : J → ℕ) :
    (((j : J) → MarkedRawDeletionBatch (k j) (a j)) ×
      ((j : J) → Equiv.Perm (Fin (a j)))) ≃ ((j : J) → Fin (a j) ↪ Fin (k j)) where
  toFun c j := giantSignedPromotionIndexEquiv (k j) (a j) ⟨c.1 j, c.2 j⟩
  invFun e := (fun j => ((giantSignedPromotionIndexEquiv (k j) (a j)).symm (e j)).1,
    fun j => ((giantSignedPromotionIndexEquiv (k j) (a j)).symm (e j)).2)
  left_inv c := by
    apply Prod.ext
    · funext j
      exact congrArg Sigma.fst ((giantSignedPromotionIndexEquiv (k j) (a j)).symm_apply_apply
        ⟨c.1 j, c.2 j⟩)
    · funext j
      exact congrArg Sigma.snd ((giantSignedPromotionIndexEquiv (k j) (a j)).symm_apply_apply
        ⟨c.1 j, c.2 j⟩)
  right_inv e := by
    funext j
    exact (giantSignedPromotionIndexEquiv (k j) (a j)).apply_symm_apply (e j)

theorem giantSignedPromotionFamily_sum {J : Type*} [Fintype J] [DecidableEq J]
    (k a : J → ℕ) (F : ((j : J) → Fin (a j) ↪ Fin (k j)) → ℂ) :
    (∑ e, F e) = ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (a j),
      ∑ σ : (j : J) → Equiv.Perm (Fin (a j)),
        F (fun j => giantSignedPromotionEmbedding ⟨S j, σ j⟩) := by
  classical
  rw [← Equiv.sum_comp (giantSignedPromotionFamilyEquiv k a) F, Fintype.sum_prod_type]
  rfl

def giantSignedRetrievalSurvivors {X : Type*} {n a : ℕ}
    (e : Fin a ↪ Fin (n + a)) (old : Fin (n + a) → X) : Fin n → X :=
  markedRawSurvivorTupleCast (Finset.univ.map e)
    (by simp only [Finset.card_compl, Fintype.card_fin, Finset.card_map, Finset.card_univ]; omega) old

theorem giantSignedPromotionEmbedding_retrieved {X : Type*} {n a : ℕ}
    (S : MarkedRawDeletionBatch (n + a) a) (σ : Equiv.Perm (Fin a))
    (old : Fin (n + a) → X) :
    old ∘ giantSignedPromotionEmbedding ⟨S, σ⟩ =
      markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) old ∘ σ := by
  funext i
  apply congrArg old
  change S.1.orderEmbOfFin (markedRawDeletionBatch_deleted_card S) (σ i) =
    S.1.orderEmbOfFin rfl (Fin.cast (markedRawDeletionBatch_deleted_card S).symm (σ i))
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

theorem giantSignedPromotionEmbedding_survivors {X : Type*} {n a : ℕ}
    (S : MarkedRawDeletionBatch (n + a) a) (σ : Equiv.Perm (Fin a))
    (old : Fin (n + a) → X) :
    giantSignedRetrievalSurvivors (giantSignedPromotionEmbedding ⟨S, σ⟩) old =
      markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) old := by
  have hc (R T : Finset (Fin (n + a))) (hr : Rᶜ.card = n) (ht : Tᶜ.card = n)
      (h : R = T) :
      markedRawSurvivorTupleCast R hr old = markedRawSurvivorTupleCast T ht old := by
    subst T
    rfl
  exact hc _ _ _ _ (giantSignedPromotionEmbedding_image ⟨S, σ⟩)

end
end ArtinMatthews
