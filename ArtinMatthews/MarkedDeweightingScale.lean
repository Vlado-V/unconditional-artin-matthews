module

public import ArtinMatthews.MarkedEstimateDeweighting


set_option backward.privateInPublic true
@[expose] public section

/-! The scale-preserving Cauchy step converts two prime-mass bounds into
the precise common scale needed for marked deweighting. -/

namespace ArtinMatthews

open scoped BigOperators

theorem marked_deweighting_from_scaled_mass_bounds {ι : Type*} (S : Finset ι)
    (w d : ι → ℝ) (a : ι → ℂ) {A B t : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hmass : ∑ i ∈ S, w i ≤ A * t) (hvariance : ∑ i ∈ S, w i * d i ^ 2 ≤ B * t) :
    ‖∑ i ∈ S, (w i : ℂ) * a i * (d i : ℂ)‖ ≤ Real.sqrt (A * B) * t := by
  have h := marked_deweighting_of_mass_bounds S w d a hw (by norm_num : (0 : ℝ) ≤ 1)
    ha hmass hvariance
  simp only [one_mul, Real.sqrt_mul hA, Real.sqrt_mul hB] at h
  calc
    _ ≤ (Real.sqrt A * Real.sqrt t) * (Real.sqrt B * Real.sqrt t) := h
    _ = (Real.sqrt A * Real.sqrt B) * (Real.sqrt t * Real.sqrt t) := by ring
    _ = Real.sqrt (A * B) * t := by rw [Real.mul_self_sqrt ht, Real.sqrt_mul hA]

end ArtinMatthews
