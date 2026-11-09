module

public import ArtinMatthews.MarkedTypeIIScalarMajorMass
public import ArtinMatthews.MarkedTypeIISharedLabelSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute mass for the actual visible label pairs. The uniform bound
also applies to the coprime subset and to any literal endpoint flags. -/
namespace ArtinMatthews
noncomputable section
open Finset

theorem markedTypeIIScalarMajor_total_abs_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (L : Finset (ℕ×ℕ)) (S T N : Finset ℕ) (Z : ℕ)
    (hS : ∀ v ∈ S×ˢN,v.1*v.2 ∈ Icc 1 Z)
    (hT : ∀ v ∈ T×ˢN,v.1*v.2 ∈ Icc 1 Z)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R W A B : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (hαS : ∀ m ∈ S,‖α m‖ ≤ A) (hαT : ∀ m ∈ T,‖α m‖ ≤ A)
    (hβ : ∀ n ∈ N,‖β n‖ ≤ B)
    (hL : L ⊆ markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y)
    (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ)
    (hG : ∀ z ∈ L, ∀ v ∈ S×ˢN, ∀ w ∈ T×ˢN, ‖G z v w‖ ≤ 1) :
    (markedMajorLabelMass P)^2*
      (∑ z ∈ L, ∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN,
        ‖G z v w*markedTypeIIScalarMajorTerm η ψ Q Y α β z.1 z.2 v w‖) ≤
      64*(markedMajorLabelMass P)^2*(A*B)^2*W*(2*R+1)*Q^3*Y*(Z:ℝ)*
        (∑ d ∈ Icc 1 Z,1/(d:ℝ))^3 := by
  let C := ((A*B)^2*W*(4*Q^3/Y))*((2*R+1)*(Z:ℝ)*(∑ d ∈ Icc 1 Z,1/(d:ℝ))^3)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hc : (L.card:ℝ) ≤ (4*Y)^2 := by
    apply (Nat.cast_le.mpr (card_le_card hL)).trans
    rw [card_product,Nat.cast_mul,← pow_two]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (markedTypeIIDyadLabels_card_le P Y hY) 2
  calc
    _ ≤ (markedMajorLabelMass P)^2*(∑ _z ∈ L,C) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply sum_le_sum
      intro z hz
      obtain ⟨hb,ha⟩ := mem_product.mp (hL hz)
      exact markedTypeIIScalarMajorPair_abs_le S T N Z hS hT η ψ hQ hY hR hW hA hB
        hη hψ hsupp α β hαS hαT hβ z.1 z.2
        (mem_filter.mp hb).2.1 (mem_filter.mp ha).2.1 (G z) (hG z hz)
    _ ≤ (markedMajorLabelMass P)^2*((4*Y)^2*C) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hC) (sq_nonneg _)
    _ = _ := by
      dsimp only [C]
      field_simp [hY.ne']
      ring

end
end ArtinMatthews
