module

public import ArtinMatthews.SpectralKLDirectProperties
public import ArtinMatthews.SpectralWeylWeightedMoment
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

/-! The direct heat regularity bounds supply the weighted moment and
positive power used in the actual two-profile geometric passage. -/

noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem spectralKLHeatRegularity_measurable (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0) : Measurable F := by
  have hc := hF.1.continuousOn
  have hz : ContinuousOn F (Ioi (0 : ℝ))ᶜ := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Ioi (0 : ℝ))ᶜ).congr
    intro x hx
    exact hzero x (le_of_not_gt hx)
  have hm := hc.measurable_piecewise hz measurableSet_Ioi
  simpa only [Set.piecewise_same] using hm

theorem spectralKLHeatRegularity_common_bounds (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, 0 < x → ‖F x‖ ≤ C*x^(3/4 : ℝ)) ∧
      (∀ x : ℝ, 1 ≤ x → ‖F x‖ ≤ C/x^2) := by
  obtain ⟨_,_,⟨C,hC,hsmall⟩,hlarge⟩ := hF
  obtain ⟨D,_,hD⟩ := hlarge 2 (by norm_num)
  refine ⟨max C D,hC.trans (le_max_left _ _),?_,?_⟩
  · intro x hx
    exact (hsmall x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _))
  · intro x hx
    exact (hD x hx).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg x))

theorem spectralKLHeatRegularity_five_eighths (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0) :
    Integrable (fun x : ℝ => x^(-(5/8 : ℝ))*‖F x‖) spectralKLPhysicalMeasure ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, 0 < x → ‖F x‖ ≤ M*x^(5/8 : ℝ) := by
  obtain ⟨C,hC,hs,hl⟩ := spectralKLHeatRegularity_common_bounds F hF
  have hm := spectralKLHeatRegularity_measurable F hF hzero
  exact ⟨(spectralWeylPhysicalMoment_five_eighths F hm C hC (fun x hx _ => hs x hx) hl).1,
    C,hC,spectralWeylFiveEighths_global_power F C hC (fun x hx _ => hs x hx) hl⟩

end ArtinMatthews
