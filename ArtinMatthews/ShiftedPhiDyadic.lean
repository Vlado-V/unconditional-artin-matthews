module

public import ArtinMatthews.ShiftedRawDyadicTarget


set_option backward.privateInPublic true
@[expose] public section

/-! The source dyadic estimate with the original smooth sampling profile. -/

namespace ArtinMatthews
open Set OAI.SevenEighths
open scoped ContDiff
noncomputable section

theorem giantCubicSamplingBilinear_phi_dyadic (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∃ CΦ : ℝ, 0 < CΦ ∧
      ∀ (N : ℕ) (η : HeckeFamily.Character) (ν C : ℝ), 0 ≤ C →
        ShiftedRawDyadicBound N η ν C →
      ∀ (x : ℝ), 0 < x → ∀ M T : ℕ, 0 < M → 0 < T →
      ∀ A B : Finset ℕ, A ⊆ Finset.Icc M (2 * M) → B ⊆ Finset.Icc T (2 * T) →
        (∀ m ∈ A, Squarefree m) → (∀ m ∈ A, N.Coprime m) →
      ∀ α β : ℕ → ℂ, (∀ m ∈ A, ‖α m‖ ≤ 1) → (∀ n ∈ B, ‖β n‖ ≤ 1) →
        ‖giantCubicSamplingBilinear η Φ x A B α β‖ ≤
          CΦ * C * ((M : ℝ) * T) ^ ν *
            (Real.sqrt M * T + (M : ℝ) ^ (5 / 4 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ)) := by
  obtain ⟨CΦ, hCΦ, htransfer⟩ := giantCubicSamplingBilinear_mellin_transfer Φ hΦ hsupp
  refine ⟨CΦ, hCΦ, ?_⟩
  intro N η ν C hC hraw x hx M T hM hT A B hA hB hsf hcop α β hα hβ
  have hApos (m : ℕ) (hm : m ∈ A) : 0 < m :=
    hM.trans_le (Finset.mem_Icc.mp (hA hm)).1
  have hBpos (n : ℕ) (hn : n ∈ B) : 0 < n :=
    hT.trans_le (Finset.mem_Icc.mp (hB hn)).1
  let R := C * ((M : ℝ) * T) ^ ν *
    (Real.sqrt M * T + (M : ℝ) ^ (5 / 4 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ))
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hbound (α' β' : ℕ → ℂ) (hα' : ∀ m ∈ A, ‖α' m‖ ≤ 1) (hβ' : ∀ n ∈ B, ‖β' n‖ ≤ 1) :
      ‖shiftedRawThetaBilinear η A B α' β'‖ ≤ R :=
    hraw M T hM hT A B hA hB hsf hcop α' β' hα' hβ'
  simpa only [R, mul_assoc] using
    htransfer η x hx A B α β hApos hBpos hα hβ R hR hbound

end
end ArtinMatthews
