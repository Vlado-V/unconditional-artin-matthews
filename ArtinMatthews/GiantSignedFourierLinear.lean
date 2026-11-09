module

public import ArtinMatthews.GiantSignedFiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Linearity and weighted counting-measure Parseval for finite residue fibers. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem giantSignedFourier_sum {I : Type*} (s : Finset I)
    (f : I → G → ℂ) (χ : AddChar G ℂ) :
    giantSignedFourier (fun x => ∑ i ∈ s, f i x) χ =
      ∑ i ∈ s, giantSignedFourier (f i) χ := by
  classical
  simp only [giantSignedFourier, Finset.mul_sum]
  exact Finset.sum_comm

theorem giantSignedFourier_const_mul (c : ℂ) (f : G → ℂ) (χ : AddChar G ℂ) :
    giantSignedFourier (fun x => c * f x) χ = c * giantSignedFourier f χ := by
  classical
  simp only [giantSignedFourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem giantSignedFourier_weighted_parseval {A : Type*} [Fintype A]
    (w : A → ℝ) (f : G → A → ℂ) :
    (∑ χ : AddChar G ℂ, ∑ a, w a * ‖giantSignedFourier (fun x => f x a) χ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ x, ∑ a, w a * ‖f x a‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, giantSignedFourier_parseval]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem giantSignedFourier_energy_bound {A : Type*} [Fintype A]
    (w : A → ℝ) (U : ℝ) (f g : G → A → ℂ)
    (h : ∀ χ : AddChar G ℂ,
      (∑ a, w a * ‖giantSignedFourier (fun x => g x a) χ‖ ^ 2) ≤
        U ^ 2 * ∑ a, w a * ‖giantSignedFourier (fun x => f x a) χ‖ ^ 2) :
    (∑ x, ∑ a, w a * ‖g x a‖ ^ 2) ≤
      U ^ 2 * ∑ x, ∑ a, w a * ‖f x a‖ ^ 2 := by
  classical
  have hs := Finset.sum_le_sum (fun χ (_ : χ ∈ (Finset.univ : Finset (AddChar G ℂ))) => h χ)
  rw [← Finset.mul_sum, giantSignedFourier_weighted_parseval,
    giantSignedFourier_weighted_parseval] at hs
  have hcard : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  nlinarith

end
end ArtinMatthews
