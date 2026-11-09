module

public import ArtinMatthews.SpectralKLDirectDefinitions


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectralKLDirectSynthesis_kernel_bound (F : ℝ → ℂ)
    (hrapid : SpectralKLDirectRapid F)
    (k : ℕ) (hk : 1 < k) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, a ≤ x →
      ‖schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
          (spectralKLPlancherelWeight t : ℂ)‖ ≤ C / x ^ k / (1 + t ^ 2) := by
  obtain ⟨CK, hCK, hK⟩ := schlafliBesselK_closed_strip_polynomial_bound k 0 a
    le_rfl (by
      have hr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      linarith) ha
  obtain ⟨CF, hCF, hF⟩ := hrapid (k + 2)
  refine ⟨(2 / Real.pi ^ 2) * CK * CF * 2 ^ k, by positivity, ?_⟩
  intro x t hax
  have hK' := hK 0 t x (by norm_num) hax
  simp only [Complex.ofReal_zero, zero_add] at hK'
  have he : (Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb := spectralKLInverseKEnvelope_scalar k t x (Real.exp (Real.pi * |t| / 2)) CK CF
    ‖schlafliBesselK ((t : ℂ) * Complex.I) x‖ ‖F t‖ |spectralKLPlancherelWeight t|
    (ha.trans_le hax) (Real.exp_pos _) hCK.le hCF (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    hK' (hF t) (by rw [he]; exact spectralKLPlancherelWeight_abs_bound t)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hb


end
end ArtinMatthews
