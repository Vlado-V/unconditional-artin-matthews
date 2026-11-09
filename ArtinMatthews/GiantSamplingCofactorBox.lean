module

public import ArtinMatthews.GiantSamplingSmallSquareActual
public import ArtinMatthews.GiantSamplingLargeSquareActual


set_option backward.privateInPublic true
@[expose] public section

/-! The two squarepart estimates combined on one actual cofactor box. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

theorem giantCubicSampling_cofactorBox_norm_le (η : HeckeFamily.Character)
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (ν : ℝ) (hν : 0 < ν) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x T D C Cν : ℝ)
      (R : ℕ) (K : Finset ℕ),
      1 ≤ x → 0 < T → 4 ≤ D → D ^ 2 ≤ T → 0 < C → 0 ≤ Cν →
      (∀ k ∈ K, T ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * T) →
      (∀ k ∈ K, ‖H k‖ ≤ C) → (∀ t, ‖Φ t‖ ≤ 1) → Function.support Φ ⊆ Set.Ioo 1 2 →
      GiantSamplingShiftedBilinearBound η Φ x ν Cν →
      (∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingCofactorSum η χ H Φ ε x r K‖) ≤
        (R : ℝ) ^ 2 * (M : ℝ) ^ 2 * C * (Cν * x ^ ν) *
          (x * T ^ (-(1 / 2) : ℝ) * D ^ 2 +
            x ^ (7 / 8 : ℝ) * (2 * T) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ))) +
        Ctail * C * x ^ (1 + 2 * ν) / D := by
  obtain ⟨Ctail, hCtail, hlarge⟩ := giantCubicSampling_largeSquareRows_le η χ ν hν
  refine ⟨Ctail, hCtail, ?_⟩
  intro H Φ ε x T D C Cν R K hx hT hD hDT hC hCν hK hH hΦ hs hbilinear
  let B := ⌊2 * T⌋₊
  let S := (Finset.Icc 1 B).filter (fun d : ℕ => (d : ℝ) ≤ D)
  let L := (Finset.Icc 1 B).filter (fun d : ℕ => D < (d : ℝ))
  have hKB (k : ℕ) (hk : k ∈ K) : 0 < k ∧ k ≤ B :=
    ⟨Nat.cast_pos.mp (hT.trans_le (hK k hk).1), Nat.le_floor (hK k hk).2⟩
  have hsplit (r : ℕ) : giantCubicSamplingCofactorSum η χ H Φ ε x r K =
      giantCubicSamplingSquareRows η χ H Φ ε x r K B S +
        giantCubicSamplingSquareRows η χ H Φ ε x r K B L :=
    giantCubicSamplingCofactorSum_split_squareRows η χ H Φ ε x r K B hKB D
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (‖giantCubicSamplingSquareRows η χ H Φ ε x r K B S‖ +
        ‖giantCubicSamplingSquareRows η χ H Φ ε x r K B L‖) := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (giantCubicSampling_smallSquareRows_le η χ H Φ ε R K B
        (zero_lt_one.trans_le hx) hT (by linarith) hDT hC hCν hK hH hbilinear)
        (hlarge H Φ ε x T D C R K B hx hT hD hC.le hK hH hΦ hs)

end ArtinMatthews
