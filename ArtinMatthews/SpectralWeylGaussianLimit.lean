module

public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SpectralWeylContourShift
public import ArtinMatthews.SpectralWeylShiftedLineBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
open Set MeasureTheory Filter Complex
open scoped Topology
noncomputable section

/-- The explicit order integrand after removing the Gaussian. -/
def spectralWeylBareOrderIntegrand (cylinder : ℂ → ℝ → ℂ) (H : ℂ → ℂ)
    (X : ℝ) (z : ℂ) : ℂ := z*H z*cylinder (-2*I*z) X

theorem spectralWeylGaussian_tendsto_one (z : ℂ) :
    Tendsto (fun R : ℝ => Complex.exp (-2*(z/(R : ℂ))^2)) atTop (𝓝 1) := by
  have hi : Tendsto (fun R : ℝ => (R : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hq : Tendsto (fun R : ℝ => z/(R : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul z
  have he := Complex.continuous_exp.continuousAt.tendsto.comp ((hq.pow 2).const_mul (-2))
  simpa only [Function.comp_def,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,Complex.exp_zero] using he

theorem spectralWeylContourIntegrand_tendsto (cylinder : ℂ → ℝ → ℂ)
    (H : ℂ → ℂ) (X : ℝ) (z : ℂ) :
    Tendsto (fun R : ℝ => spectralWeylContourIntegrand cylinder H R X z) atTop
      (𝓝 (spectralWeylBareOrderIntegrand cylinder H X z)) := by
  have h := ((spectralWeylGaussian_tendsto_one z).const_mul (z*H z)).mul_const (cylinder (-2*I*z) X)
  simpa only [spectralWeylContourIntegrand,spectralWeylBareOrderIntegrand,mul_one] using h

theorem spectralWeylContour_gaussian_limit
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    (hhol : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z)
    {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X (t : ℂ)) atTop
      (𝓝 (∫ t : ℝ, spectralWeylBareOrderIntegrand cylinder H X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I))) := by
  obtain ⟨C,_,hPoint⟩ := spectralWeylContour_five_eighths_bound cylinder H base hFactor hCylinder hB
    (fun t => hBase t (5/8) (by norm_num) (by norm_num))
  let P := (X/2)^(5/4 : ℝ)*Real.exp (X^2/4)
  have hDCT : Tendsto (fun R : ℝ => ∫ t : ℝ,
      spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I)) atTop
      (𝓝 (∫ t : ℝ, spectralWeylBareOrderIntegrand cylinder H X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => (C*P)*SourcePhysical.sourceContourHeightWeight t)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      exact (spectralWeylContour_integrable_line cylinder H base hFactor hCylinder hB hBase
        hR hX (hhol R X hR hX) (y:=5/8) (by norm_num) (by norm_num)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      exact ae_of_all _ fun t => by
        simpa only [P,SourcePhysical.sourceContourHeightWeight,div_eq_mul_inv] using hPoint R X t hR hX
    · exact SourcePhysical.sourceContourHeightWeight_integrable.const_mul (C*P)
    · exact ae_of_all _ fun t => spectralWeylContourIntegrand_tendsto cylinder H X _
  apply hDCT.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  exact (spectralWeylContour_shift cylinder H base hFactor hCylinder hB hBase hR hX (hhol R X hR hX)).symm

theorem spectralWeylBareOrder_integrable_line
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    (hhol : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => spectralWeylBareOrderIntegrand cylinder H X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I)) := by
  obtain ⟨C,_,hPoint⟩ := spectralWeylContour_five_eighths_bound cylinder H base hFactor hCylinder hB
    (fun t => hBase t (5/8) (by norm_num) (by norm_num))
  let P := (X/2)^(5/4 : ℝ)*Real.exp (X^2/4)
  have hF : Continuous (fun t : ℝ => spectralWeylContourIntegrand cylinder H 1 X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hhol 1 X le_rfl hX _ (by norm_num) (by norm_num)).continuousAt.comp (by fun_prop)
  have hG : Continuous (fun t : ℝ => Complex.exp (-2*((t : ℂ)+((5/8 : ℝ) : ℂ)*I)^2)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => spectralWeylBareOrderIntegrand cylinder H X ((t : ℂ)+((5/8 : ℝ) : ℂ)*I)) := by
    apply (hF.div hG (fun t => Complex.exp_ne_zero _)).congr
    intro t
    let z : ℂ := (t : ℂ)+((5/8 : ℝ) : ℂ)*I
    change spectralWeylContourIntegrand cylinder H 1 X z / Complex.exp (-2*z^2) =
      spectralWeylBareOrderIntegrand cylinder H X z
    simp only [spectralWeylContourIntegrand,spectralWeylBareOrderIntegrand,Complex.ofReal_one,div_one]
    calc
      _ = (z*H z*cylinder (-2*I*z) X)*Complex.exp (-2*z^2)/Complex.exp (-2*z^2) := by ring
      _ = _ := mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)
  apply (SourcePhysical.sourceContourHeightWeight_integrable.const_mul (C*P)).mono' hcont.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    apply le_of_tendsto (spectralWeylContourIntegrand_tendsto cylinder H X _).norm
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    simpa only [P,SourcePhysical.sourceContourHeightWeight,div_eq_mul_inv] using hPoint R X t hR hX

end
end ArtinMatthews
