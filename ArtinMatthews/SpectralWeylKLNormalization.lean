module

public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralBesselKIConnection
public import ArtinMatthews.SpectralKLPhysicalCompactData
public import ArtinMatthews.SpectralWeylGaussianJImaginary
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
open Set MeasureTheory Complex OAI.CubicEisenstein
noncomputable section

theorem spectralWeyl_full_line_half_sum (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ t : ℝ, F t) = ∫ t in Ioi (0 : ℝ), F t+F (-t) := by
  rw [integral_add hF.integrableOn hF.comp_neg.integrableOn,
    integral_comp_neg_Ioi, neg_zero]
  simpa only [compl_Ioi] using (integral_add_compl measurableSet_Ioi hF).symm

theorem spectralWeylJ_density_normalization (H : ℂ → ℂ)
    (hH : ∀ z : ℂ, H (-z) = H z) (R : ℝ) {X t : ℝ}
    (hX : 0 < X) (ht : 0 < t) :
    (spectralKLPlancherelWeight t : ℂ)*spectralWeylJMultiplier t X*
        H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) =
      (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
        (spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x) H R X (t : ℂ)+
          spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x) H R X ((-t : ℝ) : ℂ)) := by
  have hs : (Real.sinh (Real.pi*t) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  have hx : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [spectralKLPlancherelWeight,spectralWeylJMultiplier,ite_eq_left hX,
    spectralWeylContourIntegrand,Complex.ofReal_neg,neg_div,neg_sq,hH]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
  rw [show -2*I*(-(t : ℂ)) = ((2*t : ℝ) : ℂ)*I by push_cast;ring,
    show -2*I*(t : ℂ) = ((-2*t : ℝ) : ℂ)*I by push_cast;ring]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  field_simp [hs,hx,hp]
  ring

theorem spectralWeylK_density_normalization (H : ℂ → ℂ)
    (hH : ∀ z : ℂ, H (-z) = H z) (R : ℝ) {X t : ℝ}
    (hX : 0 < X) (_ht : 0 < t) :
    (spectralKLPlancherelWeight t : ℂ)*spectralWeylKMultiplier t X*
        H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) =
      (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
        (spectralWeylContourIntegrand spectralBesselI H R X (t : ℂ)+
          spectralWeylContourIntegrand spectralBesselI H R X ((-t : ℝ) : ℂ)) := by
  let ν : ℂ := ((2*t : ℝ) : ℂ)*I
  have hν : |ν.re| < 1/2 := by simp [ν]
  have hki := schlafliBesselK_eq_I_difference hν hX
  have hsin : Complex.sin ((Real.pi : ℂ)*ν) =
      I*((2*Real.sinh (Real.pi*t)*Real.cosh (Real.pi*t) : ℝ) : ℂ) := by
    dsimp [ν]
    rw [spectral_sin_pi_imaginary]
    congr 1
    rw [show Real.pi*(2*t) = 2*(Real.pi*t) by ring,Real.sinh_two_mul]
  rw [hsin] at hki
  have hx : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [spectralKLPlancherelWeight,spectralWeylKMultiplier,ite_eq_left hX,
    spectralWeylContourIntegrand,Complex.ofReal_neg,neg_div,neg_sq,hH]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
  have hn : -2*I*(t : ℂ) = -ν := by dsimp [ν];push_cast;ring
  have hpν : -2*I*(-(t : ℂ)) = ν := by dsimp [ν];push_cast;ring
  rw [hn,hpν]
  change _ = _
  dsimp [ν] at hki ⊢
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at hki ⊢
  field_simp [hx,hp]
  linear_combination (-8*I*(t : ℂ)*H (t : ℂ))*hki +
    (16*(t : ℂ)*(Real.sinh (Real.pi*t) : ℂ)*(Real.cosh (Real.pi*t) : ℂ)*
      schlafliBesselK (2*(t : ℂ)*I) X*H (t : ℂ))*I_sq

theorem spectralWeylGaussian_normalization (M : ℝ → ℝ → ℂ) (H : ℂ → ℂ)
    (R X : ℝ) (F : ℝ → ℂ) (hF : Integrable F)
    (hpoint : ∀ t : ℝ, 0 < t →
      (spectralKLPlancherelWeight t : ℂ)*M t X*H (t : ℂ)*
          Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) =
        (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*(F t+F (-t))) :
    Integrable (fun t : ℝ => M t X*H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
        spectralKLSpectralMeasure ∧
      (∫ t : ℝ, M t X*H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)
        ∂spectralKLSpectralMeasure) =
        (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*(∫ t : ℝ, F t) := by
  have hp : ∀ t : ℝ, 0 < t → 0 ≤ spectralKLPlancherelWeight t :=
    fun _ ht => (spectralKLPlancherelWeight_pos ht).le
  have hsum := (hF.add hF.comp_neg).const_mul (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))
  have hi : IntegrableOn (fun t : ℝ => (spectralKLPlancherelWeight t : ℂ)*
      (M t X*H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))) (Ioi (0 : ℝ)) := by
    apply hsum.integrableOn.congr_fun _ measurableSet_Ioi
    intro t ht
    simpa only [Pi.add_apply,mul_assoc] using (hpoint t ht).symm
  constructor
  · exact (spectralKLPositiveWeightMeasure_complex_integrable_iff _ _
      spectralKLPlancherelWeight_continuous.measurable hp).mpr hi
  · rw [spectralKLSpectralMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
      spectralKLPlancherelWeight_continuous.measurable hp]
    calc
      _ = ∫ t in Ioi (0 : ℝ), (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*(F t+F (-t)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa only [mul_assoc] using hpoint t ht
      _ = (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*(∫ t in Ioi (0 : ℝ), F t+F (-t)) := by
        rw [integral_const_mul]
      _ = _ := by rw [← spectralWeyl_full_line_half_sum F hF]

theorem spectralWeylJGaussian_eq_contour (H : ℂ → ℂ)
    (hH : ∀ z : ℂ, H (-z) = H z) (R : ℝ) {X : ℝ} (hX : 0 < X)
    (hF : Integrable (fun t : ℝ => spectralWeylContourIntegrand
      (fun ν x => Complex.besselJ ν x) H R X (t : ℂ))) :
    Integrable (fun t : ℝ => spectralWeylJMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) spectralKLSpectralMeasure ∧
      (∫ t : ℝ, spectralWeylJMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure) =
        (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
          (∫ t : ℝ, spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x) H R X (t : ℂ)) :=
  spectralWeylGaussian_normalization _ H R X _ hF
    (fun _t ht => spectralWeylJ_density_normalization H hH R hX ht)

theorem spectralWeylKGaussian_eq_contour (H : ℂ → ℂ)
    (hH : ∀ z : ℂ, H (-z) = H z) (R : ℝ) {X : ℝ} (hX : 0 < X)
    (hF : Integrable (fun t : ℝ => spectralWeylContourIntegrand spectralBesselI H R X (t : ℂ))) :
    Integrable (fun t : ℝ => spectralWeylKMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) spectralKLSpectralMeasure ∧
      (∫ t : ℝ, spectralWeylKMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure) =
        (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
          (∫ t : ℝ, spectralWeylContourIntegrand spectralBesselI H R X (t : ℂ)) :=
  spectralWeylGaussian_normalization _ H R X _ hF
    (fun _t ht => spectralWeylK_density_normalization H hH R hX ht)

end
end ArtinMatthews
