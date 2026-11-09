module

public import ArtinMatthews.MarkedActualDeweighting
public import ArtinMatthews.MarkedLimsupScale


set_option backward.privateInPublic true
@[expose] public section

/-! The exact normalized limsup form of positive prime deweighting. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

noncomputable def markedPrimeDeweightingError {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (Φ : ℝ → ℝ) (T : ℝ) (F : ℝ → ℕ → ℂ) (x : ℝ) : ℝ :=
  ‖∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
    (Φ ((u : ℝ) / x) : ℂ) * F x u *
      (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ)‖

/-- Equation (2.10), with a concrete constant independent of the number
of arrays and of their fixed exponents. Bounds on the test coefficients
are required only at prime predecessors. -/
theorem marked_actual_prime_deweighting_limsup {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C) :
    limsup (fun x => Real.log x / x * markedPrimeDeweightingError e Φ T F x) atTop ≤
      C * markedPrimeDeweightingConstant (Fintype.card I) (1 / 960048) 20000 Φ T /
        Real.sqrt (Fintype.card J) := by
  apply marked_normalized_limsup_le
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact marked_actual_prime_deweighting_canonical e he hinj hJ
      Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF

/-- The constant in the exact prime-deweighting limsup tends to zero as
the number of arrays increases, while the number of bands stays fixed. -/
theorem marked_prime_deweighting_limsup_constant_decay (K : ℕ)
    (Φ : ℝ → ℝ) (T C : ℝ) :
    Tendsto (fun b : ℕ => C * markedPrimeDeweightingConstant K (1 / 960048) 20000 Φ T /
      Real.sqrt b) atTop (𝓝 0) :=
  marked_deweighting_array_count_decay _

end ArtinMatthews
