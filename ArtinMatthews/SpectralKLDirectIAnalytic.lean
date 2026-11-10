module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralBesselIOrderAnalytic
public import ArtinMatthews.SpectralBesselIStripBound
public import ArtinMatthews.SpectralKLInverseIShift
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectralKLDirectIIntegrand_differentiableAt (F : ℂ → ℂ)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im)
    (hF : DifferentiableAt ℂ F z) :
    DifferentiableAt ℂ (spectralKLDirectIIntegrand F x) z := by
  have horder : -(1 / 2 : ℝ) < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have hI := (spectralBesselI_order_differentiableAt hx horder).comp z
    ((hasDerivAt_id z).const_mul (-Complex.I)).differentiableAt
  exact (differentiableAt_id.mul hF).mul hI

theorem spectralKLDirectIIntegrand_strip_bound (F : ℂ → ℂ)
    (hrapid : SpectralKLDirectStripRapid F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y x : ℝ, 0 ≤ y → y ≤ 3 / 4 → 0 < x →
      ‖spectralKLDirectIIntegrand F x ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C * Real.exp x * x ^ y / (1 + t ^ 2) := by
  obtain ⟨K, hK, hk⟩ := hrapid 3
  obtain ⟨J, hJ, hI⟩ := spectralBesselI_closed_strip_exp_bound (3 / 4) (by norm_num)
  refine ⟨2 * K * J, by positivity, ?_⟩
  intro t y x hy0 hyB hx
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hiorder : -Complex.I * z = (y : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    dsimp [z]
    push_cast
    linear_combination -(y : ℂ) * Complex.I_sq
  have hz : ‖z‖ ≤ 1 + |t| := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |t| + y := by rw [norm_mul]; simp [abs_of_nonneg hy0]
      _ ≤ _ := by linarith
  have hk' := hk t y (by rw [abs_of_nonneg hy0]; exact hyB)
  have hi := hI y (-t) x hy0 hyB hx
  rw [abs_neg, Real.exp_add] at hi
  rw [← hiorder] at hi
  have hb := spectralKLInverseIEnvelope_scalar t (Real.exp (Real.pi * |t| / 2))
    1 K J (Real.exp x) (x ^ y) ‖z‖ 1 ‖F z‖ ‖spectralBesselI (-Complex.I * z) x‖
    (Real.exp_pos _) zero_le_one hK hJ.le (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _)
    (norm_nonneg _) zero_le_one (norm_nonneg _) (norm_nonneg _)
    hz (by nlinarith [sq_nonneg t]) hk' (by simpa only [mul_assoc] using hi)
  simpa only [spectralKLDirectIIntegrand, norm_mul, z, mul_one, one_mul, mul_assoc] using hb

theorem spectralKLDirectIIntegrand_integrable_line (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F)
    {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
    Integrable (fun t : ℝ => spectralKLDirectIIntegrand F x
      ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨C, _, henv⟩ := spectralKLDirectIIntegrand_strip_bound F hrapid
  have hcont : Continuous (fun t : ℝ => spectralKLDirectIIntegrand F x
      ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have him : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    exact (spectralKLDirectIIntegrand_differentiableAt F hx
      (by rw [him]; linarith) (hF _ (by rwa [him]) (by rwa [him]))).continuousAt.comp
      (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (C * Real.exp x * x ^ y)).mono' hcont.aestronglyMeasurable
  exact ae_of_all _ fun t => by simpa only [div_eq_mul_inv, mul_assoc] using henv t y x hy0 hyB hx

theorem spectralKLDirectIIntegrand_shift (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, spectralKLDirectIIntegrand F x (t : ℂ)) =
      ∫ t : ℝ, spectralKLDirectIIntegrand F x ((t : ℂ) + (3 / 4 : ℂ) * Complex.I) := by
  obtain ⟨C, hC, henv⟩ := spectralKLDirectIIntegrand_strip_bound F hrapid
  apply spectral_horizontal_shift_of_power_bound (spectralKLDirectIIntegrand F x) x C hx hC
  · intro z hz0 hzB
    exact spectralKLDirectIIntegrand_differentiableAt F hx (by linarith) (hF z hz0 hzB)
  · exact fun t y hy0 hyB => henv t y x hy0 hyB hx

end
end ArtinMatthews
