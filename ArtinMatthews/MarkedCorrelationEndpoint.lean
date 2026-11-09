module

public import ArtinMatthews.MarkedCorrelationLimit
public import ArtinMatthews.MarkedCorrelationNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The exact correlation endpoint after the ordered finite-array limits.
The single-array marked estimate remains an explicit analytic input. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_actual_correlation_isLittleO_of_marked
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C)
    (c A : ℝ) (n₀ : ℕ)
    (hmarked : ∀ n ≥ n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5) → Function.Injective e →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖markedPrimeSingleArrayCorrelation e Φ T F x‖ ≤
          A * Real.exp (-(2 * (n : ℝ))) /
            (markedCorrelationSieveExponent c (2 * n)) ^ 2 + ε) :
    markedPrimeCorrelation Φ T F =o[atTop] (fun x : ℝ => x / Real.log x) := by
  apply marked_correlation_isLittleO_of_normalized_norm
  exact marked_actual_correlation_norm_tendsto_of_marked
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF c A n₀ hmarked

end ArtinMatthews
