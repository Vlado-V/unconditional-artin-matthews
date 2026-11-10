module

public import ArtinMatthews.GiantSignedSmallEdgeKernel
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

/-! Exact pointwise reversal of the actual small residue weight. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type*} [Fintype S] {PS : S → Finset ℕ} {k ell : ℕ}

private theorem small_pattern_abs_reverse
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    {C : S → Finset (Fin k)} (d : ℤ) {q : ℝ} (hq : 0 ≤ q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PS C ell)
    (s t : GiantTwoSidedResidueState PS (k+ell)) (aux : GiantTwoSidedPatternAuxiliary PS C) :
    ‖giantTwoSidedResiduePatternCoefficient d q ζ K s t aux‖ =
      ‖giantTwoSidedResiduePatternCoefficient (-d) q ζ (fun a b c => K b a c) t s aux‖ := by
  have h : GiantTwoSidedResiduePatternCondition C d s t aux ↔
      GiantTwoSidedResiduePatternCondition C (-d) t s aux := by
    constructor
    · exact giantTwoSidedResiduePatternCondition_reverse C d s t aux
    · intro h
      simpa only [neg_neg] using giantTwoSidedResiduePatternCondition_reverse C (-d) t s aux h
  rw [giantTwoSidedResiduePatternCoefficient_norm hPS hVS _ hq,
    giantTwoSidedResiduePatternCoefficient_norm hPS hVS _ hq, ← h]
  split_ifs
  · ring
  · rfl

theorem giantSignedSmallEdgeWeight_reverse
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (κ : ℤ) (D : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (s t : GiantTwoSidedResidueState PS (k+ell)) :
    giantSignedSmallEdgeWeight κ D q s t = giantSignedSmallEdgeWeight (-κ) D q t s := by
  unfold giantSignedSmallEdgeWeight
  rw [neg_mul]
  exact small_pattern_abs_reverse hPS hVS (κ * (D : ℤ)) hq 0 _ s t _

end
end ArtinMatthews
