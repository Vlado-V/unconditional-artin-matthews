module

public import ArtinMatthews.GiantSignedTraceAdmissibleWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The unrestricted guarded boundary equals the finite sum over the
actual admissible distinct-birth traces when that carrier is finite. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem giantSignedGuardedTraceBoundaryPairing_eq_admissibleBirth_sum
    {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)
    [Finite (GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K)] :
    let T := GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K
    letI : Fintype T := Fintype.ofFinite T
    let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)
    giantSignedGuardedTraceBoundaryPairing ν rows
      (giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)) =
        ∑ t : T,
          ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν t.2.1 : ℝ) : ℂ)*
            giantSignedTraceWeight giantSignedBoundary rows (t.1,t.2.1,giantSignedEmptyMemory PB) t.2.2.val := by
  intro T rows
  let totalFintype : Fintype T := Fintype.ofFinite T
  let Small := GiantTwoSidedResidueState PS (k+ell)
  let Active := MarkedPhysicalMarking PB (k+ell)
  let start (y : Small) (a : Active) : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
  let Fiber (y : Small) (a : Active) :=
    GiantSignedAdmissibleBirthTraceAt ν V q ρ θ patterns C κ visitQ ζ K (start y a)
  have finiteFiber (y : Small) (a : Active) : Finite (Fiber y a) :=
    Finite.of_injective (fun t : Fiber y a => (⟨y,a,t⟩ : T)) (by
      intro t v hv
      have h : (⟨a,t⟩ : Σ b : Active, Fiber y b) = ⟨a,v⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hv).2
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  letI : ∀ y a, Fintype (Fiber y a) := fun y a => @Fintype.ofFinite _ (finiteFiber y a)
  let weight (y : Small) (a : Active) (t : GiantSignedTrace rows (start y a)) :=
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ)*
      giantSignedTraceWeight giantSignedBoundary rows (start y a) t
  let canonical : Fintype T := (Sigma.instFintype : Fintype (Σ y : Small, Σ a : Active, Fiber y a))
  have huniv : @Finset.univ T totalFintype = @Finset.univ T canonical :=
    congrArg (@Finset.univ T) (Subsingleton.elim _ _)
  have hflat : (@Finset.sum T ℂ _ (@Finset.univ T canonical) (fun t => weight t.1 t.2.1 t.2.2.val)) =
      ∑ y : Small, ∑ a : Active, ∑ t : Fiber y a, weight y a t.val :=
    (Fintype.sum_sigma (fun t : Σ y : Small, Σ a : Active, Fiber y a => weight t.1 t.2.1 t.2.2.val)).trans
      (Finset.sum_congr rfl (fun y _ =>
        Fintype.sum_sigma (fun t : Σ a : Active, Fiber y a => weight y t.1 t.2.val)))
  rw [huniv,hflat]
  unfold giantSignedGuardedTraceBoundaryPairing
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  rw [← tsum_mul_left, ← tsum_fintype (L := SummationFilter.unconditional (Fiber y a))]
  let G : Set (GiantSignedTrace rows (start y a)) :=
    {t | let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1) (start y a) t
      GiantSignedChronologicalAdmissible κ z.history ∧
        GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history)}
  change _ = ∑' t : G, weight y a t.val
  rw [tsum_subtype G (weight y a)]
  apply tsum_congr
  intro t
  refine (giantSignedTraceWeightedDistinct_eq_admissible_indicator ν V q ρ θ patterns C κ visitQ ζ K y a t).trans ?_
  by_cases ht : t ∈ G
  · rw [Set.indicator_of_mem ht]
    exact ite_eq_left ht
  · rw [Set.indicator_of_notMem ht]
    exact ite_eq_right ht

end
end ArtinMatthews
