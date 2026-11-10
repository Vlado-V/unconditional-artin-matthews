module

public import ArtinMatthews.SpectralKFrameLogWindow
public import ArtinMatthews.SpectralKAdjacentOrderMoment
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

/-! A derivative energy bound on the actual compact logarithmic window.
The adjacent-order moment keeps the constant uniform in the real
spectral parameter on each dyadic band. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff

namespace ArtinMatthews

theorem spectralKFrameLogTest_deriv_energy (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384))
    (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) {D : ℝ} (hDψ : ∀ u, |deriv ψ u| ≤ D)
    (T t : ℝ) (hT : 0 < T) (ht₂ : 1+|t| ≤ 2*T) :
    (∫ u in (0 : ℝ)..spectralKFrameLength, (deriv (spectralKFrameLogTest ψ T t) u)^2) ≤
      32*(4*D^2+15/2)*T*spectralKSquareMoment 0 t := by
  let k := T/32
  let a := Real.log 2
  let b := Real.log 384
  let K := spectralRealKLogKernel k t
  let J := deriv K
  let G := spectralKFrameLogTest ψ T t
  let I := spectralKSquareMoment 0 t
  have hk : 0 < k := by dsimp only [k]; positivity
  have ha : 0 ≤ a := (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  have hb : b ≤ spectralKFrameLength :=
    (Real.log_lt_log (by norm_num : (0 : ℝ)<384) (by norm_num : (384 : ℝ)<768)).le
  have hA : k*Real.exp a = T/16 := by
    dsimp only [k,a]
    rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
    ring
  have hK : ContDiff ℝ 1 K := spectralRealKLogKernel_contDiff_one hk t
  have hJ (u : ℝ) : J u = (k*Real.exp u)*deriv (spectralKLRealKernel t) (k*Real.exp u) :=
    (spectralRealKLogKernel_hasDerivAt hk t u).deriv
  have hG (u : ℝ) : deriv G u = deriv ψ u*K u+ψ u*J u := by
    rw [hJ]
    exact spectralKFrameLogTest_deriv ψ hψ T t u hT
  have hGcont : Continuous (deriv G) :=
    (spectralKFrameLogTest_contDiff_one ψ hψ T t hT).continuous_deriv (by simp)
  have hI₁ : IntegrableOn (fun u => 2*D^2*(K u)^2) (Icc a b) :=
    hK.continuous.pow 2 |>.integrableOn_Icc |>.const_mul _
  have hI₂ : IntegrableOn (fun u => 2*(J u)^2) (Icc a b) :=
    (hK.continuous_deriv (by simp)).pow 2 |>.integrableOn_Icc |>.const_mul _
  have hpoint (u : ℝ) : (deriv G u)^2 ≤ 2*D^2*(K u)^2+2*(J u)^2 := by
    have hDsq : (deriv ψ u)^2 ≤ D^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hDψ u) 2
    rw [hG u]
    calc
      _ ≤ 2*(deriv ψ u*K u)^2+2*(ψ u*J u)^2 := by nlinarith [sq_nonneg (deriv ψ u*K u-ψ u*J u)]
      _ = 2*(deriv ψ u)^2*(K u)^2+2*(ψ u)^2*(J u)^2 := by ring
      _ ≤ _ := by
        have hψsq : (ψ u)^2 ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (h01 u).1 (h01 u).2 2
        exact add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDsq (by norm_num)) (sq_nonneg _))
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψsq (by norm_num : 0 ≤ (2:ℝ))) (sq_nonneg (J u)))
  have hsupport : (∫ u in Icc (0 : ℝ) spectralKFrameLength, (deriv G u)^2) =
      ∫ u in Icc a b, (deriv G u)^2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (Icc_subset_Icc ha hb)
    intro u hu
    have hz : ψ u = 0 := image_eq_zero_of_notMem_tsupport (fun h => hu.2 (hSupp h))
    have hd : deriv ψ u = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hu.2 (hSupp (tsupport_deriv_subset h)))
    rw [hG u,hz,hd,zero_mul,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  have hKsq : IntegrableOn (fun x : ℝ => (spectralKLRealKernel t x)^2) (Ioi 0) := by
    simpa only [mul_zero,pow_zero,one_mul] using spectralKSquareMoment_integrable 0 t
  have h₀ : (∫ u in Ioc a b, (K u)^2) ≤ (T/16)⁻¹*I := by
    have h := spectral_scaledExp_Ioc_nonneg_moment_bound (fun x => (spectralKLRealKernel t x)^2)
      (fun _ => sq_nonneg _) hKsq hk a b
    rw [hA] at h
    simpa only [K,spectralRealKLogKernel,I,spectralKSquareMoment,mul_zero,pow_zero,one_mul] using h
  have h₁ : (∫ u in Ioc a b, (J u)^2) ≤ (T/16)⁻¹*((3/2)*(t^2+1/4)*I) := by
    have h := spectral_scaledExp_Ioc_nonneg_moment_bound
      (fun x => x^2*(deriv (spectralKLRealKernel t) x)^2) (fun _ => by positivity)
      (spectralKLRealKernel_deriv_square_integrable t) hk a b
    rw [hA] at h
    simpa only [hJ,mul_pow] using h.trans
      (mul_le_mul_of_nonneg_left (spectralKLRealKernel_deriv_square_moment_bound t)
        (inv_nonneg.mpr (by positivity)))
  have hI0 : 0 ≤ I := by
    change 0 ≤ spectralKSquareMoment 0 t
    rw [spectralKSquareMoment_zero]
    positivity
  have hTsmall : (1/2 : ℝ) ≤ T := by linarith [abs_nonneg t]
  have hTsq : (1/4 : ℝ) ≤ T^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/2) hTsmall 2
    norm_num at h
    exact h
  have ht_abs : |t| ≤ 2*T := by linarith
  have htsq : t^2 ≤ 4*T^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
    rw [sq_abs,mul_pow] at h
    norm_num at h
    exact h
  have hCoeff : D^2+(3/2)*(t^2+1/4) ≤ (4*D^2+15/2)*T^2 := by
    have hh : 0 ≤ D^2*(4*T^2-1) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  rw [intervalIntegral.integral_of_le spectralKFrameLength_pos.le,← integral_Icc_eq_integral_Ioc,hsupport]
  change _ ≤ 32*(4*D^2+15/2)*T*I
  calc
    _ ≤ ∫ u in Icc a b, 2*D^2*(K u)^2+2*(J u)^2 :=
      setIntegral_mono_on ((hGcont.pow 2).integrableOn_Icc) (hI₁.add hI₂)
        measurableSet_Icc (fun u _ => hpoint u)
    _ = 2*D^2*(∫ u in Ioc a b, (K u)^2)+2*(∫ u in Ioc a b, (J u)^2) := by
      rw [integral_add hI₁ hI₂,integral_const_mul,integral_const_mul,
        integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc]
    _ ≤ 2*D^2*((T/16)⁻¹*I)+2*((T/16)⁻¹*((3/2)*(t^2+1/4)*I)) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity)) (mul_le_mul_of_nonneg_left h₁ (by norm_num))
    _ = (32/T)*(D^2+(3/2)*(t^2+1/4))*I := by
      rw [inv_div]
      ring
    _ ≤ (32/T)*((4*D^2+15/2)*T^2)*I :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoeff (by positivity)) hI0
    _ = _ := by field_simp [hT.ne']

end ArtinMatthews
