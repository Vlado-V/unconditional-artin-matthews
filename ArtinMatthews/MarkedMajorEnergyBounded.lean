module

public import ArtinMatthews.MarkedMajorArcCoefficientBounds
public import ArtinMatthews.MarkedSparsePhaseContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! Global finite bounds for the actual coefficient polynomials. These
are used only to justify Mellin/Fubini integrability, not for cancellation. -/
namespace ArtinMatthews
open Finset

theorem markedNaturalPolynomial_norm_le (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖markedNaturalPolynomial S a t‖ ≤ ∑ n ∈ S,‖a n‖ := by
  unfold markedNaturalPolynomial
  simpa only [norm_mul,markedPrimePhase_norm,mul_one] using
    norm_sum_le S (fun n => a n*markedPrimePhase n t)

theorem marked_centered_sum_bounded {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation H u v : ℝ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorCenteredSum χ W modulation t H u v‖ ≤ B := by
  refine ⟨∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,‖(H:ℂ)⁻¹*(markedMajorCenteredCoefficient W modulation n*χ (n:ZMod q))‖,?_⟩
  intro t
  rw [marked_centered_sum_eq_natural]
  exact markedNaturalPolynomial_norm_le _ _ _

theorem marked_dyadic_sum_bounded (l r : ℕ) (U : ℝ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedDyadicPolynomial l r U β t‖ ≤ B := by
  refine ⟨(∑ n ∈ Icc l r,‖β n‖)/|U|,?_⟩
  intro t
  unfold markedDyadicPolynomial
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg U)
  simpa only [norm_mul,markedPrimePhase_norm,mul_one] using
    norm_sum_le (Icc l r) (fun n => β n*markedPrimePhase n t)

end ArtinMatthews
