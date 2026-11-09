module

public import ArtinMatthews.CubicSamplingBaselineCRT
public import ArtinMatthews.GiantMarkedCharacterCriterion


set_option backward.privateInPublic true
@[expose] public section

/-! The actual centered Section 6 coefficient test splits into the literal
giant-prime count and its original reciprocal-mass baseline. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantCubicSamplingCenteredSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ) (r : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    H u * giantMarkedCenteredCore ε x u * giantCubicSamplingKernel η χ Φ x r u

theorem giantCubicSamplingCenteredSum_eq (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ)
    {ε x : ℝ} (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) (r : ℕ) :
    giantCubicSamplingCenteredSum η χ H Φ ε x r =
      giantCubicSamplingGiantSum η χ H Φ ε x r -
        (giantPrimeReciprocalSum x ε : ℂ) * giantCubicSamplingBaselineSum η χ H Φ x r := by
  unfold giantCubicSamplingCenteredSum giantCubicSamplingGiantSum giantCubicSamplingBaselineSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hu₁, hu₂⟩ := Finset.mem_Icc.mp hu
  have hux : (u : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr hu₂).trans (Nat.floor_le (by positivity))
  rw [giantMarkedCenteredCore, boundedGiantIndicator_eq_card hu₁ hux hx hε]
  push_cast
  ring

end ArtinMatthews
