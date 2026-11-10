module

public import ArtinMatthews.FullMainFixedCutoff
public import ArtinMatthews.FullMainPhysicalInputs
public import ArtinMatthews.GiantComparisonActualCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal performed comparison bound closes the ordinary tuple
input at the fixed main-theorem cutoff. -/
namespace ArtinMatthews

open Set
open scoped ContDiff
noncomputable section

theorem giantMainOrdinaryTupleCancellationInput_actual :
    GiantOrdinaryTupleCancellationInput giantMainEpsilon giantMainSmoothCutoff := by
  apply giantMainOrdinaryTupleCancellationInput_of_comparison
  intro T hT₁ _ hs M _ m _ γ j hj χ K e he hinj
  let Ψ (t : ℝ) : ℂ := ((t*giantMainSmoothCutoff t : ℝ) : ℂ)
  have hΨ : ContDiff ℝ ∞ Ψ :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.mul giantMainSmoothCutoff_spec.1)
  have hΨs : Function.support Ψ ⊆ Icc 1 T := by
    intro t ht
    apply Ioo_subset_Icc_self
    apply hs
    intro h
    exact ht (by simp [Ψ,h])
  have hγ : 0 < γ :=
    markedSieveExponent_pos (div_pos giantMainEpsilon_bounds.1 (by norm_num)) m
  have hj₀ : 0 < j := zero_lt_two.trans_le (Finset.mem_Icc.mp hj).1
  exact giantCandidatePerformedComparisonLogSaving_actual e he hinj
    giantMainEpsilon_bounds.1 (giantMainEpsilon_bounds.2.trans (by norm_num))
    (Nat.pos_of_ne_zero (NeZero.ne M)) χ hγ j hj₀ (by norm_num) (by norm_num)
    Ψ zero_lt_one hT₁.le hΨ hΨs

theorem fullMainStatement_of_angular_input
    (hsource : GiantAngularSourceInput) : FullMainStatement :=
  fullMainStatement_of_fixed_tuple_angular_inputs giantMainOrdinaryTupleCancellationInput_actual hsource

end
end ArtinMatthews
