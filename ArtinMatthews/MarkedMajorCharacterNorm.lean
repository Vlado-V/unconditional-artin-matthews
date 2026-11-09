module

public import ArtinMatthews.MarkedMajorCharacterArc


set_option backward.privateInPublic true
@[expose] public section

/-! Exact six-character coefficient cost for the fixed-arc source sum. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajor_arc_character_norm (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (h : ℤ) (θ Y : ℝ)
    (hA : ∀ z ∈ S,A z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q))
    (hB : ∀ z ∈ T,B z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q)) :
    ‖markedMajorArcSourceSum S T A B ψ q h θ Y‖ ≤
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,
        ‖markedFourierCoeff (markedResiduePhase q h) χ‖ * ‖markedMajorArcCharacterTerm S T A B ψ q χ θ Y‖ := by
  rw [markedMajor_arc_character_expansion S T A B ψ q h θ Y hA hB]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

theorem markedMajor_arc_character_norm_le (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (h : ℤ) (θ Y : ℝ)
    (hA : ∀ z ∈ S,A z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q))
    (hB : ∀ z ∈ T,B z ≠ 0 → IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q))
    {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ χ,‖markedMajorArcCharacterTerm S T A B ψ q χ θ Y‖ ≤ E) :
    ‖markedMajorArcSourceSum S T A B ψ q h θ Y‖ ≤ (q:ℝ)^6*E := by
  calc
    _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ,
      ‖markedFourierCoeff (markedResiduePhase q h) χ‖*‖markedMajorArcCharacterTerm S T A B ψ q χ θ Y‖ :=
        markedMajor_arc_character_norm S T A B ψ q h θ Y hA hB
    _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ, ‖markedFourierCoeff (markedResiduePhase q h) χ‖*E :=
      sum_le_sum (fun χ _ => mul_le_mul_of_nonneg_left (hbound χ) (norm_nonneg _))
    _ = (∑ χ : AddChar (MarkedUnitTuple q) ℂ, ‖markedFourierCoeff (markedResiduePhase q h) χ‖)*E :=
      (sum_mul ..).symm
    _ ≤ (q:ℝ)^6*E := mul_le_mul_of_nonneg_right (markedResiduePhase_total_norm_le q h) hE

end
end ArtinMatthews
