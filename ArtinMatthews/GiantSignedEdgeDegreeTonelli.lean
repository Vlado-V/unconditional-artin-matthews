module

public import ArtinMatthews.GiantSignedEdgeFixedJoint
public import ArtinMatthews.GiantSignedEdgeDegreeShift
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Exact removal of the retrieved degree in the full pending-memory sum. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem ennreal_tsum_three_rotate {A B C : Type*} (F : A → B → C → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, F a b c) = ∑' c, ∑' a, ∑' b, F a b c := by
  calc
    _ = ∑' a, ∑' c, ∑' b, F a b c := by
      apply tsum_congr
      intro a
      exact ENNReal.tsum_comm
    _ = _ := ENNReal.tsum_comm

theorem ennreal_tsum_five_reorder {A M S T B : Type*}
    (F : A → M → S → T → B → ℝ≥0∞) :
    (∑' a, ∑' m, ∑' s, ∑' t, ∑' b, F a m s t b) =
      ∑' s, ∑' t, ∑' a, ∑' b, ∑' m, F a m s t b := by
  calc
    _ = ∑' s, ∑' a, ∑' m, ∑' t, ∑' b, F a m s t b :=
      ennreal_tsum_three_rotate (fun a m s => ∑' t, ∑' b, F a m s t b)
    _ = ∑' s, ∑' t, ∑' a, ∑' m, ∑' b, F a m s t b := by
      apply tsum_congr
      intro s
      exact ennreal_tsum_three_rotate (fun a m t => ∑' b, F a m s t b)
    _ = _ := by
      apply tsum_congr
      intro s
      apply tsum_congr
      intro t
      apply tsum_congr
      intro a
      exact ENNReal.tsum_comm

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

theorem giantSignedEdgeMemory_tsum_shift
    (T : (j : J) → Finset (Fin (t j)))
    (F : (m : GiantSignedMemory P) →
      ((j : J) → Fin (T j).card ↪ Fin (m.1 j)) → ℝ≥0∞) :
    (∑' m : GiantSignedMemory P, ∑ e, F m e) =
      ∑' n : J → ℕ, ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card),
        ∑ e, F ⟨fun j => n j + (T j).card, old⟩ e := by
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype]
  apply giantSignedDegreeShift_tsum (fun j => (T j).card)
  intro k hk
  apply Finset.sum_eq_zero
  intro old _
  apply Finset.sum_eq_zero
  intro e _
  apply False.elim
  apply hk
  intro j
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (e j) (e j).injective

end
end ArtinMatthews
