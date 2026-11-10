module

public import ArtinMatthews.SourceComplexGaussianFourier
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

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap FourierTransform RealInnerProductSpace
noncomputable section

theorem source_complex_gaussian_mellin_fourier (f : 𝓢(ℂ, ℂ)) (s : ℂ) :
    mellin (sourceComplexGaussianPairing (𝓕 f : 𝓢(ℂ, ℂ))) s =
      ((Real.pi : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ) ^ (s - 1)) *
        mellin (sourceComplexGaussianPairing f) (1 - s) := by
  let B : ℝ → ℂ := fun t => sourceComplexGaussianPairing f (Real.pi ^ 2 * t)
  calc
    _ = mellin (fun t : ℝ => (Real.pi : ℂ) • ((t : ℂ) ^ (-1 : ℂ) • B t⁻¹)) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [source_complex_gaussian_pairing_fourier f t ht]
      simp only [B, Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    _ = (Real.pi : ℂ) * mellin (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) • B t⁻¹) s := by
      rw [mellin_const_smul, smul_eq_mul]
    _ = (Real.pi : ℂ) * mellin B (1 - s) := by
      rw [mellin_cpow_smul, mellin_comp_inv]
      congr 2
      ring
    _ = _ := by
      dsimp only [B]
      rw [mellin_comp_mul_left _ _ (sq_pos_of_pos Real.pi_pos), smul_eq_mul]
      rw [show -(1 - s) = s - 1 by ring]
      ring

/-- The local complex zeta functional equation in the open critical strip,
derived from Gaussian Fourier duality and an absolutely convergent Mellin integral. -/
theorem source_complex_zeta_functional_equation (f : 𝓢(ℂ, ℂ)) (a : ℝ)
    (ha : 0 < a) (ha2 : a < 2) :
    (Real.Gamma (a / 2) : ℂ) *
        (∫ z : ℂ, (𝓕 f : 𝓢(ℂ, ℂ)) z * ((‖z‖ ^ (-a) : ℝ) : ℂ)) =
      ((Real.pi : ℂ) * ((Real.pi ^ 2 : ℝ) : ℂ) ^ (((a / 2 : ℝ) : ℂ) - 1)) *
        ((Real.Gamma ((2 - a) / 2) : ℂ) *
          (∫ z : ℂ, f z * (‖z‖ ^ (-(2 - a)) : ℝ))) := by
  have hl := source_complex_zeta_gaussian_mellin (𝓕 f : 𝓢(ℂ, ℂ)) a ha ha2
  have hr := source_complex_zeta_gaussian_mellin f (2 - a) (by linarith) (by linarith)
  have he : (((2 - a) / 2 : ℝ) : ℂ) = 1 - ((a / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he] at hr
  rw [hl, source_complex_gaussian_mellin_fourier, ← hr]

theorem source_complex_zeta_fourier_nonzero (f : 𝓢(ℂ, ℂ)) (a : ℝ)
    (ha : 0 < a) (ha2 : a < 2)
    (hf : (∫ z : ℂ, f z * (‖z‖ ^ (-(2 - a)) : ℝ)) ≠ 0) :
    (∫ z : ℂ, (𝓕 f : 𝓢(ℂ, ℂ)) z * ((‖z‖ ^ (-a) : ℝ) : ℂ)) ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpp : ((Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 Real.pi_ne_zero)
  have hg : (Real.Gamma ((2 - a) / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))
  intro hz
  have h := source_complex_zeta_functional_equation f a ha ha2
  rw [hz, mul_zero] at h
  exact (mul_ne_zero (mul_ne_zero hp (Complex.cpow_ne_zero_iff.mpr (Or.inl hpp)))
    (mul_ne_zero hg hf)) h.symm

end
end ArtinMatthews.VaryingKummerAnalytic
