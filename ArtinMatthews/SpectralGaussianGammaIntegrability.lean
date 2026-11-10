module

public import ArtinMatthews.SpectralGaussianGammaSeries
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute L1 convergence of the Gaussian gamma series, from counting
measure Fubini.  This establishes integrability of the actual summed function. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace ArtinMatthews

theorem spectralGaussianGammaSeries_product_integrable (a b z : ℂ) (ha : 0 < a.re) :
    Integrable (fun p : ℕ × ℝ => spectralGaussianGammaTerm a b z p.1 p.2)
      (Measure.count.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℕ × ℝ => spectralGaussianGammaTerm a b z p.1 p.2) := by
    apply measurable_from_prod_countable_right
    intro n
    unfold spectralGaussianGammaTerm
    dsimp only
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (spectralGaussianGammaTerm_integrable a b z ha)
  · apply integrable_count_iff.mpr
    have hn (n : ℕ) : 0 ≤ ∫ x in Ioi (0 : ℝ), ‖spectralGaussianGammaTerm a b z n x‖ :=
      integral_nonneg (fun x => norm_nonneg _)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _)] using
      spectralGaussianGammaTerm_norm_summable a b z ha

theorem spectralGaussianGammaSeries_integrable (a b z : ℂ) (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, spectralGaussianGammaTerm a b z n x) (Ioi (0 : ℝ)) := by
  have h := spectralGaussianGammaSeries_product_integrable a b z ha
  apply h.integral_prod_right.congr
  filter_upwards [h.prod_left_ae] with x hx
  rw [integral_countable hx]
  simp

end ArtinMatthews
