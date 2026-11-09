module

public import ArtinMatthews.PrimeExtractionRelevantBoxes


set_option backward.privateInPublic true
@[expose] public section

/-! The selected actual dyadic boxes have a fixed positive power lower
bound on each endpoint, as required by Proposition 2.1. -/

namespace ArtinMatthews

open Filter

theorem prime_extraction_half_power_le_eventually {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, x ^ (γ/2) ≤ x ^ γ / 2 := by
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < γ/2)).eventually
    (eventually_ge_atTop (2 : ℝ)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have heq : x ^ γ = x ^ (γ/2) * x ^ (γ/2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [heq]
  nlinarith

theorem primeExtractionRelevantBoxes_geometry_eventually {a T γ : ℝ}
    (hT : 0 ≤ T) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
      a*x/4 ≤ primeExtractionDyadicHeight kl.1 kl.2 ∧
        primeExtractionDyadicHeight kl.1 kl.2 ≤ T*x ∧
        x^(γ/2) ≤ (2 : ℝ)^kl.1 ∧ x^(γ/2) ≤ (2 : ℝ)^kl.2 := by
  filter_upwards [prime_extraction_half_power_le_eventually hγ,
    eventually_ge_atTop (0 : ℝ)] with x hx hx0
  intro kl hkl
  have hg := primeExtractionRelevantBoxes_geometry (Nat.floor_le (mul_nonneg hT hx0)) hkl
  exact ⟨hg.1, hg.2.1, hx.trans hg.2.2.1.le, hx.trans hg.2.2.2.le⟩

end ArtinMatthews
