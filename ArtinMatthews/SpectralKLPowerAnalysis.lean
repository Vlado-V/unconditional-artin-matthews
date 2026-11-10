module

public import ArtinMatthews.SpectralKLIntegrableAnalysis
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralKOrderDominance
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
noncomputable section

theorem spectralKLPower_analysis_integrable (f : ℝ → ℂ) (hf : Measurable f)
    (M B β : ℝ) (_hM : 0 ≤ M) (hβ : 0 ≤ β) (hβB : β < B)
    (hpower : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ M * x ^ B)
    (ν : ℂ) (hν : |ν.re| ≤ β) :
    IntegrableOn (fun x : ℝ => schlafliBesselK ν x * (f x / (x : ℂ))) (Ioi (0 : ℝ)) := by
  have hKi : IntegrableOn (fun x : ℝ => x ^ (B - 1) * ‖schlafliBesselK (β : ℂ) x‖) (Ioi (0 : ℝ)) :=
    spectralK_power_integrable β B (by simpa only [abs_of_nonneg hβ] using hβB)
  have hKcont : ContinuousOn (schlafliBesselK ν) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (schlafliBesselK_hasDerivAt ν x hx).continuousAt.continuousWithinAt
  have hd : Measurable (fun x : ℝ => f x / (x : ℂ)) := hf.div Complex.continuous_ofReal.measurable
  apply (hKi.const_mul M).mono' (hKcont.aestronglyMeasurable measurableSet_Ioi |>.mul hd.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  dsimp only [Pi.mul_apply]
  have hk := schlafliBesselK_order_norm_le β hβ hν hx
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hx.le]
  calc
    _ ≤ ‖schlafliBesselK (β : ℂ) x‖ * ((M * x ^ B) / x) := by gcongr; exact hpower x hx
    _ = M * (x ^ (B - 1) * ‖schlafliBesselK (β : ℂ) x‖) := by
      rw [Real.rpow_sub hx, Real.rpow_one]
      ring

theorem spectralKLPower_majorant_integrable (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 < B)
    (hpower : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ M * x ^ B) :
    Integrable (spectralKLIntegrableMajorant f) := by
  have hi := (spectralKLPower_analysis_integrable f hf M B 0 hM le_rfl hB hpower 0 (by simp)).norm
  have hieq : IntegrableOn (spectralKLIntegrableMajorant f) (Ioi (0 : ℝ)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hk0 : schlafliBesselK 0 x = (spectralKLRealKernel 0 x : ℂ) := by
      simpa only [Complex.ofReal_zero, zero_mul] using schlafliBesselK_imaginary_eq_realKernel 0 hx
    rw [spectralKLIntegrableMajorant, spectralKLPhysicalCompactDiv, norm_mul, hk0]
    simp only [Complex.norm_real,
      Real.norm_of_nonneg spectralKLRealKernel_zero_nonneg]
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hieq
  intro x hx
  by_contra hn
  have hfx := hfzero x (le_of_not_gt hn)
  exact hx (by simp [spectralKLIntegrableMajorant, spectralKLPhysicalCompactDiv, hfx])

end
end ArtinMatthews
