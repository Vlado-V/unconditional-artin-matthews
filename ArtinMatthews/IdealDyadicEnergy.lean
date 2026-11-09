module

public import ArtinMatthews.IdealDyadicPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Reassembly of the exact dyadic decomposition uses only the
original full-tuple energies and the finite number of occupied dyads. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealProductDyadicPart_energy_le {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ x, 0 ≤ μ x) (p : A → ℕ) (j : ℕ) (f : A → ℂ) :
    idealFrameEnergy μ (idealProductDyadicPart p j f) ≤ idealFrameEnergy μ f := by
  unfold idealFrameEnergy
  apply sum_le_sum
  intro x _
  by_cases hx : Nat.log 2 (p x) = j
  · simp only [idealProductDyadicPart, ite_eq_left hx, le_refl]
  · simp only [idealProductDyadicPart, ite_eq_right hx, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (hμ x) (sq_nonneg _)

theorem idealDyadicPairing_sq_le {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℕ) (q : B → ℕ) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (f : A → ℂ) (g : B → ℂ) (K : A → B → ℂ) (ε : ℝ)
    (hpiece : ∀ j ∈ idealProductDyads p, ∀ k ∈ idealProductDyads q,
      ‖∑ x, (μ x : ℂ)*idealProductDyadicPart p j f x*
        ∑ y, (ν y : ℂ)*idealProductDyadicPart q k g y*K x y‖^2 ≤
      ε^2*idealFrameEnergy μ (idealProductDyadicPart p j f)*
        idealFrameEnergy ν (idealProductDyadicPart q k g)) :
    ‖∑ x, (μ x : ℂ)*f x*∑ y, (ν y : ℂ)*g y*K x y‖^2 ≤
      ((idealProductDyads p).card : ℝ)^2*((idealProductDyads q).card : ℝ)^2*
        ε^2*idealFrameEnergy μ f*idealFrameEnergy ν g := by
  rw [idealProductDyadic_pairing]
  have hF := idealFrameEnergy_nonneg μ hμ f
  have hG := idealFrameEnergy_nonneg ν hν g
  have hb := idealFinitePairing_sq_le (idealProductDyads p) (idealProductDyads q)
    (fun j k => ∑ x, (μ x : ℂ)*idealProductDyadicPart p j f x*
      ∑ y, (ν y : ℂ)*idealProductDyadicPart q k g y*K x y)
    (E := ε^2*idealFrameEnergy μ f*idealFrameEnergy ν g)
    (fun j hj k hk => (hpiece j hj k hk).trans (by
      have hprod := mul_le_mul (idealProductDyadicPart_energy_le μ hμ p j f)
        (idealProductDyadicPart_energy_le ν hν q k g)
        (idealFrameEnergy_nonneg ν hν _) hF
      have hm := mul_le_mul_of_nonneg_left hprod (sq_nonneg ε)
      simpa only [mul_assoc] using hm))
  convert hb using 1
  ring

end
end ArtinMatthews
