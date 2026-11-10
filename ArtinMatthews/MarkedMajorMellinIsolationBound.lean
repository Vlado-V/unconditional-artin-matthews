module

public import ArtinMatthews.MarkedMajorMellinIsolationBase
public import ArtinMatthews.MarkedMajorMellinIsolationDerivatives
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
public import Mathlib.Tactic.ReduceModChar
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles


set_option backward.privateInPublic true
@[expose] public section

/-! Actual uniform L¹ bound for the normalized Mellin coefficient. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap
noncomputable section

private theorem fourier_weighted_norm_le_three_integrals
    (g : SchwartzMap ℝ ℂ) (u : ℝ) :
    (1+u^2)*‖(𝓕 g) u‖ ≤ 5*((∫ z : ℝ, ‖iteratedFDeriv ℝ 0 g z‖) +
      (∫ z : ℝ, ‖iteratedFDeriv ℝ 1 g z‖) +
      (∫ z : ℝ, ‖iteratedFDeriv ℝ 2 g z‖)) := by
  have h₀ := OAI.FourierBridge.fourier_seminorm_from_derivative_integrals g 0
  have h₂ := OAI.FourierBridge.fourier_seminorm_from_derivative_integrals g 2
  simp [Finset.sum_range_succ,Function.Embedding.sectR] at h₀ h₂ ⊢
  change _ ≤ (2:ℝ)^2 * (((∫ v : ℝ, |v|^0 * ‖iteratedFDeriv ℝ 0 g v‖) +
    (∫ v : ℝ, |v|^0 * ‖iteratedFDeriv ℝ 1 g v‖)) +
    (∫ v : ℝ, |v|^0 * ‖iteratedFDeriv ℝ 2 g v‖)) at h₂
  simp only [pow_zero,one_mul] at h₂
  simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one] at h₂
  have hp₀ := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) u
  have hp₂ := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 g) 2 u
  simp only [Real.norm_eq_abs,sq_abs] at hp₂
  have hi₁ : 0 ≤ ∫ z : ℝ, ‖iteratedFDeriv ℝ 1 g z‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hi₂ : 0 ≤ ∫ z : ℝ, ‖iteratedFDeriv ℝ 2 g z‖ := integral_nonneg (fun _ => norm_nonneg _)
  simp only [norm_iteratedFDeriv_one] at hi₁
  nlinarith

theorem markedMellinIsolation_coefficient_decay
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ξ : ℝ,
      ‖markedMellinIsolationCoefficient η hη ha hsupp θ ξ‖ ≤
        C*(1+|θ|)^2*(1+ξ^2)⁻¹ := by
  obtain ⟨B,hB,hbound⟩ := markedMellinIsolation_first_three_integrals_bound η hη ha hsupp
  let c : ℝ := 2*Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨5*(c+c⁻¹)*B,by positivity,?_⟩
  intro θ ξ
  let g := markedMellinIsolationSchwartz η hη ha hsupp θ
  let J := (∫ z : ℝ, ‖iteratedFDeriv ℝ 0 g z‖) +
      (∫ z : ℝ, ‖iteratedFDeriv ℝ 1 g z‖) +
      (∫ z : ℝ, ‖iteratedFDeriv ℝ 2 g z‖)
  have hpoint : (1+(ξ/c)^2)*‖(𝓕 g) (ξ/c)‖ ≤ 5*J :=
    fourier_weighted_norm_le_three_integrals g (ξ/c)
  have hnorm : ‖markedMellinIsolationCoefficient η hη ha hsupp θ ξ‖ =
      c⁻¹*‖(𝓕 g) (ξ/c)‖ := by
    rw [markedMellinIsolationCoefficient_apply,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hc.le)]
  have hscale : (1+ξ^2)*c⁻¹ ≤ (c+c⁻¹)*(1+(ξ/c)^2) := by
    have he : (c+c⁻¹)*(1+(ξ/c)^2)-(1+ξ^2)*c⁻¹ = c+c⁻¹*(ξ/c)^2 := by
      field_simp
      ring
    nlinarith [mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg (ξ/c))]
  have hscaled := mul_le_mul_of_nonneg_right hscale (norm_nonneg ((𝓕 g) (ξ/c)))
  have hp := mul_le_mul_of_nonneg_left hpoint (show 0 ≤ c+c⁻¹ by positivity)
  have hj : J ≤ B*(1+|θ|)^2 := hbound θ
  have hb := mul_le_mul_of_nonneg_left hj (show 0 ≤ 5*(c+c⁻¹) by positivity)
  rw [hnorm]
  apply (le_mul_inv_iff₀ (show 0 < 1+ξ^2 by positivity)).mpr
  nlinarith

theorem markedMellinIsolation_coefficient_L1_bound
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      (∫ ξ : ℝ, ‖markedMellinIsolationCoefficient η hη ha hsupp θ ξ‖) ≤
        C*(1+|θ|)^2 := by
  obtain ⟨C,hC,hbound⟩ := markedMellinIsolation_coefficient_decay η hη ha hsupp
  refine ⟨C*Real.pi,by positivity,?_⟩
  intro θ
  have h := integral_mono
    (markedMellinIsolationCoefficient η hη ha hsupp θ).integrable.norm
    (integrable_inv_one_add_sq.const_mul (C*(1+|θ|)^2)) (hbound θ)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at h
  nlinarith

end
end ArtinMatthews
