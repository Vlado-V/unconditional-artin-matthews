module

public import ArtinMatthews.GiantComparisonStripActual
public import ArtinMatthews.IdealResidualFamily


set_option backward.privateInPublic true
@[expose] public section

/-! In a comparison pattern both character-cell kernels read only
unshared labels. The literal source cores and character satisfy the
arithmetic conditions of the guarded quotient identity. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

def giantComparisonSelectedFreeMarking (A B S : Finset (J × Fin k))
    (hS : S ⊆ A ∪ B)
    (b : GiantComparisonFreeLabels P (idealResidualCopied (some (A,B))) ell) :
    IdealSelectedLabels (idealResidualBands P S) :=
  fun v => b v.val.1 (Sum.inl
    ⟨v.val.2, (mem_idealResidualFreeSlots (A ∪ B) v.val.1 v.val.2).mpr (hS v.property)⟩)

theorem idealResidualSelectedMarking_join_free (A B S : Finset (J × Fin k))
    (hS : S ⊆ A ∪ B)
    (c : GiantComparisonSharedLabels P (idealResidualCopied (some (A,B))))
    (b : GiantComparisonFreeLabels P (idealResidualCopied (some (A,B))) ell) :
    idealResidualSelectedMarking S (giantComparisonJoinLabels c b) =
      giantComparisonSelectedFreeMarking A B S hS b := by
  funext v
  exact giantComparisonJoinLabels_free c b v.val.1 (Sum.inl
    ⟨v.val.2, (mem_idealResidualFreeSlots (A ∪ B) v.val.1 v.val.2).mpr (hS v.property)⟩)

variable [Fintype J]

def giantComparisonFreeCoefficient (A B : Finset (J × Fin k)) (Q : ℕ) (h ξ : ℝ)
    (b b' : GiantComparisonFreeLabels P (idealResidualCopied (some (A,B))) ell)
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied (some (A,B)))) : ℂ :=
  -(-1:ℂ)^(A.card+B.card)*
    idealCharacterCellKernel (idealResidualBands P A) Q h ξ
      (idealResidualSelectedAuxiliary A
        (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_left B hv)) aux)
      (giantComparisonSelectedFreeMarking A B A subset_union_left b')*
    idealCharacterCellKernel (idealResidualBands P B) Q h ξ
      (idealResidualSelectedAuxiliary B
        (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_right A hv)) aux)
      (giantComparisonSelectedFreeMarking A B B subset_union_right b)

theorem idealResidualCoefficient_join_free (A B : Finset (J × Fin k)) (Q : ℕ) (h ξ : ℝ)
    (c : GiantComparisonSharedLabels P (idealResidualCopied (some (A,B))))
    (b b' : GiantComparisonFreeLabels P (idealResidualCopied (some (A,B))) ell)
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied (some (A,B)))) :
    idealResidualCoefficient P Q h ξ (some (A,B)) (giantComparisonJoinLabels c b)
        (giantComparisonJoinLabels c b') aux =
      giantComparisonFreeCoefficient A B Q h ξ b b' aux := by
  dsimp only [idealResidualCoefficient, giantComparisonFreeCoefficient]
  rw [idealResidualSelectedMarking_join_free A B A subset_union_left,
    idealResidualSelectedMarking_join_free A B B subset_union_right]

theorem giantCandidateComparisonPattern_sum_eq_shared_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j : ℕ)
    (q : ℝ) (Ψ : ℝ → ℂ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (k N : ℕ)
      (Z Z' : Finset ℕ), Z ⊆ Ioc 0 N →
      ∀ (A B : Finset (S × Fin k)) (Q : ℕ) (h ξ : ℝ),
      let P (g : S) := giantCandidateGroup x g.val
      let C := idealResidualCopied (some (A,B))
      let K : GiantTwoSidedPatternCoefficient P C 1 := idealResidualCoefficient P Q h ξ (some (A,B))
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      (∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ∑ s : GiantTwoSidedEndpointState P (k+1) Z,
        ∑ t : GiantTwoSidedEndpointState P (k+1) Z',
          giantComparisonPhysicalSummand x q Ψ χ F G K s t aux) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ∑ a : GiantComparisonSharedEdge P C 1 N Z Z' aux,
          giantComparisonSharedSummand x q Ψ χ F G K a := by
  filter_upwards [giantCandidateComparisonSharedInvariant_eventually e he hεq m hm γ j,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (0:ℝ)] with x hi hg hp hx
  intro S k N Z Z' hZ A B Q h ξ
  let P (g : S) := giantCandidateGroup x g.val
  let C := idealResidualCopied (some (A,B))
  have hP (g : S) (p : ℕ) (hp' : p ∈ P g) : p.Prime :=
    (hp p (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp'⟩)).1
  exact giantComparisonPhysical_sum_eq_shared hP (hg S).1 hZ hx q Ψ χ _ _ _
    (fun c w hw => (hi S k C c w hw).1) (fun c w hw => (hi S k C c w hw).2.1)
    (fun c => (hi S k C c 1 Nat.one_pos).2.2)

end
end ArtinMatthews
