module

public import ArtinMatthews.SpectralKFramePhysicalTest
public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralFiniteFourierFrame
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

/-! The actual principal K transform of each physical frame test
is its logarithmic Fourier moment. The two real phase components
give the exact squared norm of the complex moment. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped ContDiff

namespace ArtinMatthews

theorem spectralKFramePhysicalTest_principal_transform (ψ χ : ℝ → ℝ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T t : ℝ) (hT : 0 < T) :
    (∫ x : ℝ, (spectralKFramePhysicalTest ψ χ T x : ℂ)*
      schlafliBesselK ((t : ℂ)*Complex.I) x ∂spectralKLPhysicalMeasure) =
      ((∫ u in (0 : ℝ)..spectralKFrameLength, (spectralKFrameLogTest ψ T t u)*χ u : ℝ) : ℂ) := by
  let F := spectralKFramePhysicalTest ψ χ T
  let f (x : ℝ) := (F x : ℂ)*schlafliBesselK ((t : ℂ)*Complex.I) x
  have hz (x : ℝ) (hx : x ∉ Ioc (T/32) (24*T)) : f x = 0 := by
    have he : F x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (spectralKFramePhysicalTest_log_support ψ χ hSupp T hT h))
    simp only [f,he,Complex.ofReal_zero,zero_mul]
  change (∫ x : ℝ, f x ∂spectralKLPhysicalMeasure) = _
  rw [spectralKFrame_integral_log f T hT hz,intervalIntegral.integral_of_le spectralKFrameLength_pos.le,
    intervalIntegral.integral_of_le spectralKFrameLength_pos.le,← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  dsimp only [f,F]
  rw [spectralKFramePhysicalTest_scaledExp ψ χ T hT,
    schlafliBesselK_imaginary_eq_realKernel t (by positivity)]
  unfold spectralKFrameLogTest spectralRealKLogKernel
  push_cast
  ring

theorem spectral_fourierCoeffOn_phase_parts_sq {L : ℝ} (hL : 0 < L)
    (G : ℝ → ℝ) (hG : Continuous G) (m : ℤ) :
    (∫ u in (0 : ℝ)..L, G u*(cuspFourierPhase L m u).re)^2+
        (∫ u in (0 : ℝ)..L, G u*(cuspFourierPhase L m u).im)^2 =
      L^2*‖fourierCoeffOn hL (fun u => (G u : ℂ)) m‖^2 := by
  let f (u : ℝ) := cuspFourierPhase L m u*(G u : ℂ)
  let z := ∫ u in Ioc (0 : ℝ) L, f u
  have hf : Continuous f :=
    (cuspFourierPhase_contDiff L m).continuous.mul (Complex.continuous_ofReal.comp hG)
  have hi : IntegrableOn f (Ioc (0 : ℝ) L) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hre : (∫ u in (0 : ℝ)..L, G u*(cuspFourierPhase L m u).re) = z.re := by
    rw [intervalIntegral.integral_of_le hL.le]
    change _ = RCLike.re (∫ u in Ioc (0 : ℝ) L, f u)
    rw [← integral_re hi]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u _
    change _ = (f u).re
    simp only [f,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_comm _ _
  have him : (∫ u in (0 : ℝ)..L, G u*(cuspFourierPhase L m u).im) = z.im := by
    rw [intervalIntegral.integral_of_le hL.le]
    change _ = RCLike.im (∫ u in Ioc (0 : ℝ) L, f u)
    rw [← integral_im hi]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u _
    change _ = (f u).im
    simp only [f,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    exact mul_comm _ _
  have hz : z = (L : ℂ)*fourierCoeffOn hL (fun u => (G u : ℂ)) m := by
    rw [spectral_fourierCoeffOn_phase_integral hL,intervalIntegral.integral_of_le hL.le]
    change z = (L : ℂ)*((L : ℂ)⁻¹*z)
    rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'),one_mul]
  rw [hre,him]
  calc
    _ = ‖z‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    _ = _ := by rw [hz,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,mul_pow]

theorem spectralKFramePhysicalTest_principal_phase_sq (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384))
    (T t : ℝ) (hT : 0 < T) (m : ℤ) :
    let Fχ (χ : ℝ → ℝ) := ∫ x : ℝ, (spectralKFramePhysicalTest ψ χ T x : ℂ)*
      schlafliBesselK ((t : ℂ)*Complex.I) x ∂spectralKLPhysicalMeasure
    let P := cuspFourierPhase spectralKFrameLength m
    ‖Fχ (fun u => (P u).re)‖^2+‖Fχ (fun u => (P u).im)‖^2 =
      spectralKFrameLength^2*‖fourierCoeffOn spectralKFrameLength_pos
        (fun u => (spectralKFrameLogTest ψ T t u : ℂ)) m‖^2 := by
  dsimp only
  rw [spectralKFramePhysicalTest_principal_transform ψ _ hSupp T t hT,
    spectralKFramePhysicalTest_principal_transform ψ _ hSupp T t hT]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact spectral_fourierCoeffOn_phase_parts_sq spectralKFrameLength_pos _
    (spectralKFrameLogTest_contDiff_one ψ hψ T t hT).continuous m

end ArtinMatthews
