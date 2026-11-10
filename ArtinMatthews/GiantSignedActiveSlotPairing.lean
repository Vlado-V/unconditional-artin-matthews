module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedStatePermutationEnergy
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
public import Mathlib.Tactic.ENatToNat
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

/-! The original tilted active product mass permits exact source slot
reindexing against a symmetric test, with no normalization of the law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedActiveSlotPairing_fixed {B : Type*} [Fintype B] [DecidableEq B]
    {PB : B → Finset ℕ} {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (f g : MarkedPhysicalMarking PB M → ℂ) (hf : IdealSymmetric f) :
    (∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * idealSlotAverage g a) =
      ∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * g a := by
  let A := MarkedPhysicalMarking PB M
  let P := B → Equiv.Perm (Fin M)
  let W : ℂ := (Fintype.card P : ℂ)⁻¹
  let F (a : A) : ℂ := (giantSignedActiveMass ν a : ℂ) * star (f a) * g a
  have hperm (π : P) : (∑ a : A, (giantSignedActiveMass ν a : ℂ) * star (f a) *
      g (giantTwoSidedPermuteLabels π a)) = ∑ a : A, F a := by
    have h := (giantSignedGroupedTuplePermutation π).sum_comp F
    have he (a : A) : giantSignedGroupedTuplePermutation π a = giantTwoSidedPermuteLabels π a := rfl
    have hm (a : A) : giantSignedActiveMass ν (giantTwoSidedPermuteLabels π a) =
        giantSignedActiveMass ν a := giantSignedActiveMass_slot_permute ν π a
    have hfun (a : A) : f (giantTwoSidedPermuteLabels π a) = f a := hf π a
    simpa only [F, he, hm, hfun] using h
  calc
    _ = ∑ a : A, ∑ π : P, W * ((giantSignedActiveMass ν a : ℂ) * star (f a) *
        g (giantTwoSidedPermuteLabels π a)) := by
      unfold idealSlotAverage
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro π _
      dsimp only [W]
      ring
    _ = ∑ π : P, ∑ a : A, W * ((giantSignedActiveMass ν a : ℂ) * star (f a) *
        g (giantTwoSidedPermuteLabels π a)) := Finset.sum_comm
    _ = ∑ π : P, W * ∑ a : A, F a := by simp only [← Finset.mul_sum, hperm]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W]
      have hP : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [← mul_assoc, mul_inv_cancel₀ hP, one_mul]

end
end ArtinMatthews
