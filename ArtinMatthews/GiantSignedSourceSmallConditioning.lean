module

public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantSignedSourceAbsoluteCost
public import ArtinMatthews.GiantSmallConditioningNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The source small-conditioning cost is fixed before the ideal
construction and copied-slot choice. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedSourceSmallConditioning_exists
    {q vmin C₀ : ℝ} (ell : ℕ) (hq : 0 < q) (hq1 : q < 1)
    (hvmin : 0 < vmin) (hC₀ : 0 ≤ C₀) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧
      ∀ (S : Type*) [Fintype S] [DecidableEq S] (PS : S → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
        (∀ j p, p ∈ PS j → p.Prime) → Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
      ∀ (k : ℕ) (L : ℝ), 0 < L → (Fintype.card S : ℝ) ≤ C₀ * Real.log L →
      ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
        (∑ d : MarkedPhysicalMarking PS k,
          giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
            L ^ Cs * giantSmallStateEnergy f := by
  obtain ⟨BS, hBS, hbudget⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  let R := max 1 BS
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  refine ⟨C₀ * Real.log R, mul_nonneg hC₀ (Real.log_nonneg hR1), ?_⟩
  intro S _ _ PS _ hPS hdis hVmin k L hL hgroups f
  have hV (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVmin j)
  have hsmall := giantSmallConditioning_norm_sum hPS hdis hV hq hq1.le hBS
    (fun j z => hbudget _ (hVmin j) z) f
  have hcost : BS ^ Fintype.card S ≤ L ^ (C₀ * Real.log R) := calc
    _ ≤ R ^ Fintype.card S := pow_le_pow_left₀ hBS (le_max_right _ _) _
    _ = Real.exp (Real.log R * (Fintype.card S : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hR]
    _ ≤ Real.exp (Real.log L * (C₀ * Real.log R)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log R * (C₀ * Real.log L) := mul_le_mul_of_nonneg_left hgroups (Real.log_nonneg hR1)
        _ = _ := by ring
    _ = _ := (Real.rpow_def_of_pos hL _).symm
  have hf0 : 0 ≤ giantSmallStateEnergy f := by
    unfold giantSmallStateEnergy giantTwoSidedResidueHaarStateMass markedPhysicalMass
    exact mul_nonneg
      (div_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
        (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact hsmall.trans (mul_le_mul_of_nonneg_right hcost hf0)

end
end ArtinMatthews
