module

public import ArtinMatthews.GiantComparisonStripKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The physical double sum is supported on the exact comparison edges.
Taking its quotient reindexes the original auxiliary average unchanged. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell N m : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}

theorem giantComparisonPhysical_sum_support (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (aux : GiantTwoSidedPatternAuxiliary P C) :
    (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z',
        giantComparisonPhysicalSummand x q Ψ χ F G K s t aux) =
      ∑ e : GiantComparisonPhysicalEdge P C ell Z Z' aux,
        giantComparisonPhysicalSummand x q Ψ χ F G K e.val.1 e.val.2 aux := by
  classical
  let StatePair := GiantTwoSidedEndpointState P (k+ell) Z × GiantTwoSidedEndpointState P (k+ell) Z'
  let valid (p : StatePair) : Prop := GiantTwoSidedPatternCondition C 1 p.1 p.2 aux
  let term (p : StatePair) := giantComparisonPhysicalSummand x q Ψ χ F G K p.1 p.2 aux
  rw [← Fintype.sum_prod_type term]
  change (∑ p : StatePair, term p) = ∑ e : Subtype valid, term e.val
  have hs := Finset.sum_subtype (p := valid) (F := inferInstance)
    (univ.filter valid) (by simp) term
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro p _
  change term p = if valid p then term p else 0
  split_ifs with hp
  · rfl
  · have hn : ¬GiantTwoSidedPatternCondition C 1 p.1 p.2 aux := hp
    simp only [term, giantComparisonPhysicalSummand,
      giantTwoSidedPatternPhysicalCoefficient, ite_eq_right hn, mul_zero, zero_mul]

theorem giantComparisonPhysical_sum_eq_shared (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N)
    {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (hF : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      F (giantComparisonSharedProduct c*w) = F w)
    (hG : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      G (giantComparisonSharedProduct c*w) = G w)
    (hc : ∀ c : GiantComparisonSharedLabels P C, (giantComparisonSharedProduct c).Coprime m) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z',
        giantComparisonPhysicalSummand x q Ψ χ F G K s t aux) =
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ a : GiantComparisonSharedEdge P C ell N Z Z' aux,
        giantComparisonSharedSummand x q Ψ χ F G K a := by
  classical
  apply sum_congr rfl
  intro aux _
  rw [giantComparisonPhysical_sum_support]
  let term (e : GiantComparisonPhysicalEdge P C ell Z Z' aux) :=
    giantComparisonPhysicalSummand x q Ψ χ F G K e.val.1 e.val.2 aux
  change (∑ e, term e) = _
  rw [← (giantComparisonStripEquiv hP hdis hZ).symm.sum_comp term]
  apply sum_congr rfl
  intro a _
  have hw := (mem_Ioc.mp a.val.2.1.property).1
  exact giantComparisonPhysicalSummand_eq_shared hP hx q Ψ χ F G K a
    (hF a.val.1 _ hw) (hG a.val.1 _ (by omega)) (hc a.val.1)

end
end ArtinMatthews
