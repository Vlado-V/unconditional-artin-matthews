module

public import ArtinMatthews.GiantComparisonCellIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The signed finite cell sum costs exactly its two occupied cell
counts, its two primitive character counts, and the inverse mass. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidateComparisonIndependent_norm_le {x : ℝ}
    (S : Finset (GiantCandidateGroupIndex x)) {k ell M : ℕ}
    (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ) (Ψ : ℝ → ℂ) (q : ℝ) (N : ℕ)
    (hdis : Pairwise (fun g g' : S =>
      Disjoint (giantCandidateGroup x g.val) (giantCandidateGroup x g'.val))) {W : ℝ} :
    let P (g : S) := giantCandidateGroup x g.val
    let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
    let PA := idealResidualBands (giantCandidatePerformedBigBand S) A
    let PB := idealResidualBands (giantCandidatePerformedBigBand S) B
    (∀ (i : GiantComparisonCellIndex PA h Q) (j : GiantComparisonCellIndex PB h Q),
      ‖giantCandidateComparisonWeightedCell S (ell:=ell) A B χ F G Ψ q N ξ i j‖ ≤ W) →
    ‖∑ aux : GiantTwoSidedPatternAuxiliary P C, giantComparisonIndependentAuxiliarySum N x q Ψ χ F G
      (giantCandidateComparisonIndependentCoefficient S (ell:=ell) A B Q h ξ) aux‖ ≤
      (((idealLogCells PA h).card:ℝ)*((idealLogCells PB h).card:ℝ)*
        (Fintype.card (IdealPrimitiveCharacters Q):ℝ)^2*(ξ⁻¹)^2)*W := by
  intro P C PA PB hcell
  rw [giantCandidateComparisonIndependentSum_eq_cells S A B hAB Q h hξ χ F G Ψ q N hdis]
  simp only [norm_mul, norm_neg, norm_pow, norm_one, one_pow, one_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hξ]
  let X := GiantComparisonCellIndex PA h Q
  let Y := GiantComparisonCellIndex PB h Q
  have hsum :
      ‖∑ i : X, ∑ j : Y, giantCandidateComparisonWeightedCell S (ell:=ell) A B χ F G Ψ q N ξ i j‖ ≤
      (Fintype.card X:ℝ)*(Fintype.card Y:ℝ)*W := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i : X, ∑ _j : Y, W := by
        apply sum_le_sum
        intro i _
        exact (norm_sum_le _ _).trans (sum_le_sum (fun j _ => hcell i j))
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  refine (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans_eq ?_
  simp only [X, Y, GiantComparisonCellIndex, Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
  ring

end
end ArtinMatthews
