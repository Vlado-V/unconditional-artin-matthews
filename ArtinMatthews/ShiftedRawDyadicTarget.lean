module

public import ArtinMatthews.ShiftedBilinearMellinTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! The literal raw dyadic estimate, preserving the arithmetic condition on the outer variable. -/
namespace ArtinMatthews
open OAI.SevenEighths
noncomputable section

def ShiftedRawDyadicBound (N : ℕ) (η : HeckeFamily.Character) (ν C : ℝ) : Prop :=
  ∀ M T : ℕ, 0 < M → 0 < T → ∀ A B : Finset ℕ,
    A ⊆ Finset.Icc M (2 * M) → B ⊆ Finset.Icc T (2 * T) →
    (∀ m ∈ A, Squarefree m) → (∀ m ∈ A, N.Coprime m) →
    ∀ α β : ℕ → ℂ, (∀ m ∈ A, ‖α m‖ ≤ 1) → (∀ n ∈ B, ‖β n‖ ≤ 1) →
      ‖shiftedRawThetaBilinear η A B α β‖ ≤
        C * ((M : ℝ) * T) ^ ν *
          (Real.sqrt M * T + (M : ℝ) ^ (5 / 4 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ))

end
end ArtinMatthews
