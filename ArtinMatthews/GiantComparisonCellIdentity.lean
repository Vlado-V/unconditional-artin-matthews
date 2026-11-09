module

public import ArtinMatthews.GiantComparisonPerformedCells
public import ArtinMatthews.GiantComparisonIndependentExpansion
public import ArtinMatthews.GiantComparisonWeightedCell


set_option backward.privateInPublic true
@[expose] public section

/-! The restored physical comparison sum is the exact finite sum of
product-cell shifts. It keeps the original auxiliary harmonic average
and the signed inverse-mass coefficient. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {x : ℝ} (S : Finset (GiantCandidateGroupIndex x)) {k ell M : ℕ}
  (A B : Finset (GiantCandidatePerformedBig S × Fin k))

def giantCandidateComparisonWeightedCell (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ)
    (Ψ : ℝ → ℂ) (q : ℝ) (N : ℕ) {Q : ℕ} {h : ℝ} (ξ : ℝ)
    (i : GiantComparisonCellIndex (idealResidualBands (giantCandidatePerformedBigBand S) A) h Q)
    (j : GiantComparisonCellIndex (idealResidualBands (giantCandidatePerformedBigBand S) B) h Q) : ℂ :=
  let PA := idealResidualBands (giantCandidatePerformedBigBand S) A
  let PB := idealResidualBands (giantCandidatePerformedBigBand S) B
  giantComparisonWeightedCell
    (P:=fun g : S => giantCandidateGroup x g.val)
    (C:=giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) (ell:=ell)
    PA PB (giantComparisonCellIndexedFreeTest PA i) (giantComparisonCellIndexedFreeTest PB j)
    χ F G Ψ x q N
    (giantCandidateComparisonCellTest S A B B subset_union_right ξ j)
    (giantCandidateComparisonCellTest S A B A subset_union_left ξ i)

theorem giantCandidateComparisonIndependentSum_eq_cells
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ) (Ψ : ℝ → ℂ) (q : ℝ) (N : ℕ)
    (hdis : Pairwise (fun g g' : S =>
      Disjoint (giantCandidateGroup x g.val) (giantCandidateGroup x g'.val))) :
    let P (g : S) := giantCandidateGroup x g.val
    let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
    let PA := idealResidualBands (giantCandidatePerformedBigBand S) A
    let PB := idealResidualBands (giantCandidatePerformedBigBand S) B
    (∑ aux : GiantTwoSidedPatternAuxiliary P C, giantComparisonIndependentAuxiliarySum N x q Ψ χ F G
      (giantCandidateComparisonIndependentCoefficient S (ell:=ell) A B Q h ξ) aux) =
      (-(-1:ℂ)^(A.card+B.card)*((ξ:ℂ)⁻¹)^2)*
        ∑ i : GiantComparisonCellIndex PA h Q, ∑ j : GiantComparisonCellIndex PB h Q,
          giantCandidateComparisonWeightedCell S (ell:=ell) A B χ F G Ψ q N ξ i j := by
  intro P C PA PB
  let L := giantCandidateComparisonIndependentCoefficient S (ell:=ell) A B Q h ξ
  let e := giantCandidatePerformedAuxiliarySplit S A B hAB
  let T := GiantComparisonCellIndex PA h Q × GiantComparisonCellIndex PB h Q
  let α := -(-1:ℂ)^(A.card+B.card)*((ξ:ℂ)⁻¹)^2
  let s (p : T) := giantCandidateComparisonCellTest S (ell:=ell) A B B subset_union_right ξ p.2
  let t (p : T) := giantCandidateComparisonCellTest S (ell:=ell) A B A subset_union_left ξ p.1
  let f (p : T) := giantComparisonCellIndexedFreeTest PA p.1
  let g (p : T) := giantComparisonCellIndexedFreeTest PB p.2
  let d (u : IdealSelectedLabels PA) (v : IdealSelectedLabels PB) :=
    idealSelectedProduct u*idealSelectedProduct v
  have he (u : IdealSelectedLabels PA) (v : IdealSelectedLabels PB) :
      giantTwoSidedPatternAuxiliaryProduct (e.symm (u,v)) = d u v := by
    rw [giantCandidatePerformedAuxiliarySplit_product S A B hAB]
    change idealSelectedProduct (e (e.symm (u,v))).1 *
      idealSelectedProduct (e (e.symm (u,v))).2 = _
    rw [Equiv.apply_symm_apply]
  have hpair (u : IdealSelectedLabels PA) (v : IdealSelectedLabels PB) (w : ℕ) :
      ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
          giantComparisonIndependentPair L (e.symm (u,v)) q w (w+d u v) =
        ∑ p : T, (α*f p u*g p v) *
          (sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (s p) w *
           sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (t p) (w+d u v)) := by
    apply giantComparisonIndependentPair_eq_cell_expansion hdis
    intro b b'
    rw [Fintype.sum_prod_type]
    exact giantCandidateComparisonIndependentCoefficient_eq_cells S A B hAB Q h hξ b b' u v
  let J (aux : GiantTwoSidedPatternAuxiliary P C) :=
    ∑ w : ↥(Ioc 0 N), giantComparisonPositionKernel x Ψ χ F G
      (giantTwoSidedPatternAuxiliaryProduct aux) w.val *
      (((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
        giantComparisonIndependentPair L aux q w.val
          (w.val+giantTwoSidedPatternAuxiliaryProduct aux))
  have hrewrite :
      (∑ aux : GiantTwoSidedPatternAuxiliary P C,
        giantComparisonIndependentAuxiliarySum N x q Ψ χ F G L aux) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C, (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*J aux := by
    unfold giantComparisonIndependentAuxiliarySum
    apply sum_congr rfl
    intro aux _
    dsimp only [J]
    congr 1
    apply sum_congr rfl
    intro w _
    exact mul_assoc _ _ _
  change (∑ aux : GiantTwoSidedPatternAuxiliary P C,
    giantComparisonIndependentAuxiliarySum N x q Ψ χ F G L aux) = _
  rw [hrewrite, giantCandidatePerformedAuxiliarySplit_expectation S A B hAB J]
  have hTsum : (∑ p : T, giantCandidateComparisonWeightedCell S (ell:=ell) A B χ F G Ψ q N ξ p.1 p.2) =
      ∑ i : GiantComparisonCellIndex PA h Q, ∑ j : GiantComparisonCellIndex PB h Q,
        giantCandidateComparisonWeightedCell S (ell:=ell) A B χ F G Ψ q N ξ i j :=
    Fintype.sum_prod_type _
  change (∑ u : IdealSelectedLabels PA, ∑ v : IdealSelectedLabels PB,
    (idealSelectedMass PA u:ℂ)*(idealSelectedMass PB v:ℂ)*J (e.symm (u,v))) = α * _
  rw [← hTsum]
  simp only [J, he, hpair, mul_sum]
  simp_rw [sum_comm (s := (univ : Finset ↥(Ioc 0 N))) (t := (univ : Finset T))]
  simp_rw [sum_comm (s := (univ : Finset (IdealSelectedLabels PB))) (t := (univ : Finset T))]
  rw [sum_comm (s := (univ : Finset (IdealSelectedLabels PA))) (t := (univ : Finset T))]
  simp only [giantCandidateComparisonWeightedCell, giantComparisonWeightedCell, mul_sum]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  let W (w : ℕ) :=
    (idealSelectedMass PA u:ℂ)*(idealSelectedMass PB v:ℂ)*
      (giantComparisonPositionKernel x Ψ χ F G (d u v) w *
        (α*f p u*g p v *
          (sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (s p) w *
            sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (t p) (w+d u v))))
  change (∑ w : ↥(Ioc 0 N), W w.val) = _
  rw [sum_coe_sort (Ioc 0 N) W]
  apply sum_congr rfl
  intro w _
  dsimp only [W, f, g, s, t, d]
  ring

end
end ArtinMatthews
