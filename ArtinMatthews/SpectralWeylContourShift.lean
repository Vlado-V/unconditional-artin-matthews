module

public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SourceContourHeightWeight
public import ArtinMatthews.SpectralHorizontalContour
public import ArtinMatthews.SpectralWeylGammaStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

private theorem positive_strip_power_bound {x y : ℝ} (hx : 0 < x)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 5/4) : x^y ≤ 1+x^(5/4 : ℝ) := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx.le hx1 hy0).trans (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hy1).trans (le_add_of_nonneg_left zero_le_one)

theorem spectralWeylContour_height_bound
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z * spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    {R X : ℝ} (hR : 1 ≤ R) (hX : 0 < X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+(y : ℂ)*I)‖ ≤
        C*SourcePhysical.sourceContourHeightWeight t := by
  obtain ⟨G,hG,hGamma⟩ := spectral_weyl_gamma_pair_closed_strip_bound
  obtain ⟨K,hK,hRapid⟩ := spectralKLGaussianData_strip_rapid R (by linarith) 0 (5/8) (by norm_num) 3
  let E := Real.exp (25/32)
  let P := (1+(X/2)^(5/4 : ℝ))*Real.exp (X^2/4)
  refine ⟨2*B*G*P*K*(E+1), by dsimp [E,P]; positivity, ?_⟩
  intro t y hy0 hy1
  let u := 1+t^2
  have hu : 0 < u := by dsimp [u]; positivity
  have hy : |y| ≤ 5/8 := by rw [abs_of_nonneg hy0]; exact hy1
  have hZ : ‖(t : ℂ)+(y : ℂ)*I‖ ≤ 2*u := by
    calc
      _ ≤ ‖(t : ℂ)‖+‖(y : ℂ)*I‖ := norm_add_le _ _
      _ = |t|+y := by simp [abs_of_nonneg hy0]
      _ ≤ _ := by dsimp [u]; nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  have hGnorm : ‖spectralKLGaussianData R ((t : ℂ)+(y : ℂ)*I)‖ ≤ E+1 := by
    have h := spectralWeylGaussian_norm_bound hR t y hy
    rw [spectralWeylGaussian_eq_square,norm_pow] at h
    change _ ≤ E at h
    nlinarith [norm_nonneg (spectralKLGaussianData R ((t : ℂ)+(y : ℂ)*I)),Real.exp_pos (25/32)]
  have hRapid' := hRapid t y hy
  simp only [zero_mul,Real.exp_zero,mul_one] at hRapid'
  have hGaussian : u^3*‖Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2)‖ ≤ K*(E+1) := by
    rw [spectralWeylGaussian_eq_square,norm_pow,pow_two]
    calc
      _ = (u^3*‖spectralKLGaussianData R ((t : ℂ)+(y : ℂ)*I)‖)*
          ‖spectralKLGaussianData R ((t : ℂ)+(y : ℂ)*I)‖ := by ring
      _ ≤ _ := mul_le_mul hRapid' hGnorm (norm_nonneg _) hK
  have hGaussBound : ‖Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2)‖ ≤
      (K*(E+1))/u^3 := (le_div_iff₀ (pow_pos hu 3)).mpr (by simpa only [mul_comm] using hGaussian)
  have hPower : (X/2)^(2*y)*Real.exp (X^2/4) ≤ P :=
    mul_le_mul_of_nonneg_right
      (positive_strip_power_bound (half_pos hX) (by linarith) (by linarith)) (Real.exp_nonneg _)
  have hpoint := spectralWeylContourIntegrand_norm_le cylinder H base R X t y hX hy0
    (hFactor _) (hCylinder X hX)
  have hBase' := hBase t y hy0 hy1
  have hGamma' := hGamma t y hy0 hy1
  change _ ≤ B/u^2 at hBase'
  change _ ≤ G*u^3 at hGamma'
  calc
    _ ≤ (2*u)*(B/u^2)*((K*(E+1))/u^3)*P*(G*u^3) := by
      apply hpoint.trans
      gcongr
    _ = (2*B*G*P*K*(E+1))*SourcePhysical.sourceContourHeightWeight t := by
      rw [SourcePhysical.sourceContourHeightWeight]
      dsimp [u]
      field_simp

theorem spectralWeylContour_shift
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z * spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    {R X : ℝ} (hR : 1 ≤ R) (hX : 0 < X)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z) :
    (∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X (t : ℂ)) =
      ∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I) := by
  obtain ⟨C,_,hbound⟩ := spectralWeylContour_height_bound cylinder H base hFactor hCylinder hB hBase hR hX
  exact spectral_horizontal_integral_eq_of_heightWeight _ (by norm_num) hhol hbound

theorem spectralWeylContour_integrable_line
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z * spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    {R X : ℝ} (hR : 1 ≤ R) (hX : 0 < X)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 5/8) :
    Integrable (fun t : ℝ => spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+(y : ℂ)*I)) := by
  obtain ⟨C,_,hbound⟩ := spectralWeylContour_height_bound cylinder H base hFactor hCylinder hB hBase hR hX
  have hcont : Continuous (fun t : ℝ => spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+(y : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hhol _ (by simpa) (by simpa)).continuousAt.comp (by fun_prop)
  exact (SourcePhysical.sourceContourHeightWeight_integrable.const_mul C).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun t => hbound t y hy0 hy1)

end
end ArtinMatthews
