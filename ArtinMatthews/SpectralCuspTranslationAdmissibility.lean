module

public import ArtinMatthews.SpectralCuspDoubleCosetPeriod
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.AtkinLehnerMixedPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integral cusp translations and their frequency condition.  A
smaller cusp period is usable only together with its divisibility condition. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem cusp_conjugate_translation_lower (r : SL(2, ℤ)) (k : ℤ) :
    (r⁻¹ * integerTranslation k * r) 1 0 = -k * (r 1 0) ^ 2 := by
  simp [integerTranslation, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem cusp_conjugate_translation_mem_iff (N : ℕ) (r : SL(2, ℤ)) (k : ℤ) :
    r⁻¹ * integerTranslation k * r ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ k * (r 1 0) ^ 2 := by
  rw [CongruenceSubgroup.Gamma0_mem, cusp_conjugate_translation_lower,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [neg_mul, dvd_neg]

theorem atkinPhase_int (k : ℤ) : atkinPhase (k : ℝ) = 1 := by
  unfold atkinPhase
  push_cast
  rw [mul_comm (2 * ↑Real.pi * Complex.I)]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem cuspFourierPhase_as_atkinPhase (w : ℝ) (n : ℤ) (x : ℝ) :
    cuspFourierPhase w n x = atkinPhase (-(n : ℝ) * x / w) := by
  unfold cuspFourierPhase cuspFourierFrequency atkinPhase
  congr 1
  push_cast
  ring

theorem cuspFourierPhase_integer_period_of_dvd (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n * k) : cuspFourierPhase (N : ℝ) n (k : ℝ) = 1 := by
  obtain ⟨q,hq⟩ := hNk
  have hqr : (n : ℝ) * k = (N : ℝ) * q := by exact_mod_cast hq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [cuspFourierPhase_as_atkinPhase]
  have he : -(n : ℝ) * k / N = -(q : ℝ) := by
    apply (div_eq_iff hN).mpr
    nlinarith
  rw [he]
  simpa only [Int.cast_neg] using atkinPhase_int (-q)

theorem cuspFourierPhase_integer_shift_of_dvd (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n * k) (x : ℝ) :
    cuspFourierPhase (N : ℝ) n (x + k) = cuspFourierPhase (N : ℝ) n x := by
  rw [cuspFourierPhase_add, cuspFourierPhase_integer_period_of_dvd N n k hNk, mul_one]

end ArtinMatthews
