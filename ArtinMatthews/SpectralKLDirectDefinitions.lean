module

public import ArtinMatthews.SpectralKLInverseKEnvelope
public import ArtinMatthews.SpectralKLInverseIIdentity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

/-- Exponential-normalized rapid decay for data in the genuine KL spectral measure. -/
def SpectralKLDirectRapid (F : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) * ‖F t‖ ≤ C

/-- The same spectral decay throughout the strip used in the I-kernel shift. -/
def SpectralKLDirectStripRapid (F : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
    (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
      ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C

theorem spectralKLDirectStripRapid_real {F : ℂ → ℂ}
    (hF : SpectralKLDirectStripRapid F) :
    SpectralKLDirectRapid (fun t : ℝ => F (t : ℂ)) := by
  intro N
  obtain ⟨C, hC, hb⟩ := hF N
  refine ⟨C, hC, fun t => ?_⟩
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hb t 0 (by norm_num)

/-- The normalized inverse KL integral, extended by zero off the positive ray. -/
def spectralKLDirectSynthesis (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then spectralKLWeightedSynthesis F x else 0

def spectralKLDirectIIntegrand (F : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  z * F z * spectralBesselI (-Complex.I * z) x

end
end ArtinMatthews
