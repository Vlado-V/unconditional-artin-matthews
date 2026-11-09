module

public import ArtinMatthews.GiantComparisonSelectedMarkTest
public import ArtinMatthews.GiantComparisonSeparatedSum


set_option backward.privateInPublic true
@[expose] public section

/-! Separate the two free tests against the independent restored marking
measure. The source reciprocal masses and both endpoint dampings survive. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {k ell : ℕ}
  {P : J → Finset ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonIndependentPair_eq_markWeights
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (s t : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ)
    (hL : ∀ b b', L b b' aux = s (giantComparisonNumberedFreeList P C ell b) *
      t (giantComparisonNumberedFreeList P C ell b')) :
    ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
        giantComparisonIndependentPair L aux q w w' =
      sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) s w *
        sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) t w' := by
  rw [sourceComparisonMarkWeight_eq_freeMarking_sum P hdis C ell q s w,
    sourceComparisonMarkWeight_eq_freeMarking_sum P hdis C ell q t w']
  simp only [giantComparisonIndependentPair, giantComparisonIndependentDamping, hL,
    Complex.ofReal_mul, Complex.ofReal_pow, ← mul_sum, ← sum_mul]
  ring

end
end ArtinMatthews
