module

public import ArtinMatthews.GiantComparisonPerformedTest
public import ArtinMatthews.GiantComparisonSeparatedSum
public import ArtinMatthews.IdealResidualAuxiliaryAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Both actual comparison kernels separate into their retained cells
and primitive characters under the exact performed auxiliary split. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GiantComparisonCellIndex {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (h : ℝ) (Q : ℕ) :=
  ↥(idealLogCells P h) × IdealPrimitiveCharacters Q

def giantComparisonCellIndexedFreeTest {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) {h : ℝ} {Q : ℕ} (i : GiantComparisonCellIndex P h Q)
    (d : IdealSelectedLabels P) : ℂ :=
  giantComparisonCellFreeTest P h i.1.val i.2 d

theorem idealCharacterCellKernel_eq_indexed_sum {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ) (d a : IdealSelectedLabels P) :
    idealCharacterCellKernel P Q h ξ d a =
      ∑ i : GiantComparisonCellIndex P h Q, giantComparisonCellIndexedFreeTest P i d *
        giantComparisonCellMarkTest P h ξ i.1.val i.2 a := by
  rw [idealCharacterCellKernel_eq_comparison_sum, Fintype.sum_prod_type]
  exact (sum_coe_sort _ _).symm

variable {x : ℝ} (S : Finset (GiantCandidateGroupIndex x)) {k ell : ℕ}
  (A B D : Finset (GiantCandidatePerformedBig S × Fin k))

def giantCandidateComparisonCellTest (hD : D ⊆ A ∪ B) {h : ℝ} (ξ : ℝ) {Q : ℕ}
    (i : GiantComparisonCellIndex (idealResidualBands (giantCandidatePerformedBigBand S) D) h Q) :
    ((g : S) → Fin (ell+(giantCandidatePerformedPattern S
      (idealResidualCopied (some (A,B))) g).card) → ℕ) → ℂ :=
  giantCandidateComparisonNumberedTest S A B D hD (fun a =>
    (ξ:ℂ)*giantComparisonCellMarkTest (idealResidualBands (giantCandidatePerformedBigBand S) D)
      h ξ i.1.val i.2 a)

theorem giantCandidateComparisonCellTest_norm_le
    (hD : D ⊆ A ∪ B) {h ξ : ℝ} (hξ : 0 < ξ) {Q : ℕ}
    (i : GiantComparisonCellIndex (idealResidualBands (giantCandidatePerformedBigBand S) D) h Q)
    (l : (g : S) → Fin (ell+(giantCandidatePerformedPattern S
      (idealResidualCopied (some (A,B))) g).card) → ℕ) :
    ‖giantCandidateComparisonCellTest S A B D hD ξ i l‖ ≤ 1 :=
  giantCandidateComparisonNumberedTest_norm_le S A B D hD _ (fun a =>
    giantComparisonCellMarkTest_normalized_norm_le _ h hξ i.1.val i.2 a) l

def giantCandidateComparisonIndependentCoefficient (Q : ℕ) (h ξ : ℝ) :
    GiantComparisonListCoefficient (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) ell :=
  fun b b' aux => giantComparisonFreeCoefficient A B Q h ξ
    (fun g => b (giantCandidatePerformedSplitEquiv S (.inr g)))
    (fun g => b' (giantCandidatePerformedSplitEquiv S (.inr g)))
    (fun g => aux (giantCandidatePerformedSplitEquiv S (.inr g)))

theorem giantCandidateComparisonIndependentCoefficient_eq_cells
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (b b' : GiantComparisonFreeLabels (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) ell)
    (u : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) A))
    (v : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) B)) :
    let PA := idealResidualBands (giantCandidatePerformedBigBand S) A
    let PB := idealResidualBands (giantCandidatePerformedBigBand S) B
    let P (g : S) := giantCandidateGroup x g.val
    let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
    giantCandidateComparisonIndependentCoefficient S A B Q h ξ b b'
      ((giantCandidatePerformedAuxiliarySplit S A B hAB).symm (u,v)) =
        ∑ i : GiantComparisonCellIndex PA h Q, ∑ j : GiantComparisonCellIndex PB h Q,
          (-(-1:ℂ)^(A.card+B.card)*((ξ:ℂ)⁻¹)^2)*
          giantComparisonCellIndexedFreeTest PA i u *
          giantComparisonCellIndexedFreeTest PB j v *
          (giantCandidateComparisonCellTest S A B B subset_union_right ξ j
            (giantComparisonNumberedFreeList P C ell b) *
           giantCandidateComparisonCellTest S A B A subset_union_left ξ i
            (giantComparisonNumberedFreeList P C ell b')) := by
  intro PA PB P C
  unfold giantCandidateComparisonIndependentCoefficient giantComparisonFreeCoefficient
  change -(-1:ℂ)^(A.card+B.card) *
    idealCharacterCellKernel PA Q h ξ
      (idealResidualSelectedAuxiliary A _
        ((idealAuxiliarySelectedEquiv _ (A ∪ B)).symm ((idealSelectedUnionEquiv _ A B hAB).symm (u,v)))) _ *
    idealCharacterCellKernel PB Q h ξ
      (idealResidualSelectedAuxiliary B _
        ((idealAuxiliarySelectedEquiv _ (A ∪ B)).symm ((idealSelectedUnionEquiv _ A B hAB).symm (u,v)))) _ = _
  rw [idealAuxiliaryUnion_first, idealAuxiliaryUnion_second]
  let aT : IdealSelectedLabels PA := giantComparisonSelectedFreeMarking A B A subset_union_left
    (fun g => b' (giantCandidatePerformedSplitEquiv S (.inr g)))
  let bT : IdealSelectedLabels PB := giantComparisonSelectedFreeMarking A B B subset_union_right
    (fun g => b (giantCandidatePerformedSplitEquiv S (.inr g)))
  have hA (i : GiantComparisonCellIndex PA h Q) :
      giantCandidateComparisonCellTest S A B A subset_union_left ξ i
        (giantComparisonNumberedFreeList P C ell b') =
      (ξ:ℂ)*giantComparisonCellMarkTest PA h ξ i.1.val i.2 aT :=
    giantCandidateComparisonNumberedTest_free S A B A subset_union_left
      (fun a => (ξ:ℂ)*giantComparisonCellMarkTest PA h ξ i.1.val i.2 a) b'
  have hB (j : GiantComparisonCellIndex PB h Q) :
      giantCandidateComparisonCellTest S A B B subset_union_right ξ j
        (giantComparisonNumberedFreeList P C ell b) =
      (ξ:ℂ)*giantComparisonCellMarkTest PB h ξ j.1.val j.2 bT :=
    giantCandidateComparisonNumberedTest_free S A B B subset_union_right
      (fun a => (ξ:ℂ)*giantComparisonCellMarkTest PB h ξ j.1.val j.2 a) b
  change -(-1:ℂ)^(A.card+B.card) * idealCharacterCellKernel PA Q h ξ u aT *
    idealCharacterCellKernel PB Q h ξ v bT = _
  rw [idealCharacterCellKernel_eq_indexed_sum PA Q h ξ u aT,
    idealCharacterCellKernel_eq_indexed_sum PB Q h ξ v bT]
  simp only [hA, hB, mul_sum, sum_mul]
  rw [sum_comm (s := (univ : Finset (GiantComparisonCellIndex PB h Q)))
    (t := (univ : Finset (GiantComparisonCellIndex PA h Q)))]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  field_simp [Complex.ofReal_ne_zero.mpr hξ.ne'] <;> ring

end
end ArtinMatthews
