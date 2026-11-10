module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralBesselIOrderAnalytic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralKLInverseIIntegrand_differentiableAt (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im)
    (hh : DifferentiableAt ℂ h z) :
    DifferentiableAt ℂ (spectralKLInverseIIntegrand h g x) z := by
  have hK := (spectralKLCompactOrderTransform_entire g hg hc hp (Complex.I * z)).comp z
    ((hasDerivAt_id z).const_mul Complex.I).differentiableAt
  have horder : -(1 / 2 : ℝ) < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have hI := (spectralBesselI_order_differentiableAt hx horder).comp z
    ((hasDerivAt_id z).const_mul (-Complex.I)).differentiableAt
  exact ((differentiableAt_id.mul hh).mul hK).mul hI

theorem spectralKLWindowData_contDiff (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (spectralKLWindowData h g) := by
  have hK : ContDiff ℝ ∞ (spectralKLCompactOrderTransform g) :=
    (spectralKLCompactOrderTransform_entire g hg hc hp).contDiff.restrict_scalars ℝ
  have ha : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact hh.mul (hK.comp ha)

theorem spectral_positive_strip_power_bound {x y : ℝ} (hx : 0 < x)
    (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) : x ^ y ≤ 1 + x ^ (3 / 4 : ℝ) := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx.le hx1 hy0).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hyB).trans
      (le_add_of_nonneg_left (by positivity))

theorem spectralKLInverseIIntegrand_integrable_line (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (hh : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ H * (1 + t ^ 2))
    {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
    Integrable (fun t : ℝ => spectralKLInverseIIntegrand h g x
      ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, henv⟩ := spectralKLInverseIIntegrand_strip_bound h g hg hc hp H hH hbound
  have hcont : Continuous (fun t : ℝ => spectralKLInverseIIntegrand h g x
      ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have him : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    exact (spectralKLInverseIIntegrand_differentiableAt h g hg.continuous hc hp hx
      (by rw [him]; linarith) (hh _ (by rwa [him]) (by rwa [him]))).continuousAt.comp
      (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (C * Real.exp x * x ^ y)).mono' hcont.aestronglyMeasurable
  exact ae_of_all _ fun t => by simpa only [div_eq_mul_inv, mul_assoc] using henv t y x hy0 hyB hx


end
end ArtinMatthews
