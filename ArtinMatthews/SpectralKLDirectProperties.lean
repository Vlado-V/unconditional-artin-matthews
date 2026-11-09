module

public import ArtinMatthews.SpectralKLDirectContinuation
public import ArtinMatthews.SpectralKLDirectDerivatives


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectralKLDirectSynthesis_nonpositive_zero (F : ℝ → ℂ) (x : ℝ) (hx : x ≤ 0) :
    spectralKLDirectSynthesis F x = 0 := by
  simp only [spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]

/-- Regularity and both endpoint bounds for the physical KL profile. -/
def SpectralKLHeatRegularity (f : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)) ∧ MemLp f 2 spectralKLPhysicalMeasure ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
    (∀ k : ℕ, 1 < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C / x ^ k)

theorem spectralKLDirectSynthesis_regularity (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    SpectralKLHeatRegularity (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) := by
  have hR := spectralKLDirectStripRapid_real hrapid
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  exact ⟨spectralKLDirectSynthesis_contDiffOn _ hsmooth.continuous hR,
    spectralKLDirectSynthesis_memLp _ hsmooth.contDiffOn hsmooth.continuous hR,
    spectralKLDirectSynthesis_global_power_bound F heven hh hrapid,
    fun k hk => spectralKLDirectSynthesis_large_bound _ hR k hk⟩

end
end ArtinMatthews
