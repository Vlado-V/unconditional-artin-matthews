module

public import ArtinMatthews.GiantComparisonIndependentCell


set_option backward.privateInPublic true
@[expose] public section

/-! A finite character-cell decomposition can be exchanged with the
two original ordered marking sums before any analytic estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
  {k ell : ℕ} {P : J → Finset ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonIndependentPair_eq_cell_expansion
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (c : I → ℂ) (s t : I → ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ)
    (hL : ∀ b b', L b b' aux =
      ∑ i, c i * (s i (giantComparisonNumberedFreeList P C ell b) *
        t i (giantComparisonNumberedFreeList P C ell b'))) :
    ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
        giantComparisonIndependentPair L aux q w w' =
      ∑ i, c i *
        (sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (s i) w *
          sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (t i) w') := by
  let L' (i : I) : GiantComparisonListCoefficient P C ell := fun b b' _ =>
    s i (giantComparisonNumberedFreeList P C ell b) *
      t i (giantComparisonNumberedFreeList P C ell b')
  have hs : giantComparisonIndependentPair L aux q w w' =
      ∑ i, c i * giantComparisonIndependentPair (L' i) aux q w w' := by
    simp only [giantComparisonIndependentPair, hL, L', mul_sum]
    simp_rw [sum_comm (s := (univ : Finset (GiantComparisonFreeMarking P C ell w')))
      (t := (univ : Finset I))]
    rw [sum_comm (s := (univ : Finset (GiantComparisonFreeMarking P C ell w)))
      (t := (univ : Finset I))]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro b' _
    ring
  rw [hs, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← giantComparisonIndependentPair_eq_markWeights hdis (L' i) aux q w w' (s i) (t i)
    (fun _ _ => rfl)]
  ring

end
end ArtinMatthews
