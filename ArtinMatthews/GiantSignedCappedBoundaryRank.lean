module

public import ArtinMatthews.GiantSignedActualFrameBoundary
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual capped boundary admits the sign expansion on one common
frame. Its performed values still come from the original ordered trace. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

local instance giantSignedCappedBirthPermutationFintype {B : Type*} [Fintype B] {M N H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M N H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M N H)
    (GiantSignedUniformBirthAddress B M N H) inferInstance inferInstance inferInstance inferInstance

universe u
variable {S B : Type u} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)]

theorem giantSignedCappedTraceBoundaryPairing_permutation_sum {A : Type*} [Fintype A] [DecidableEq A]
    (H : ℕ) (ν : ∀ g, PB g → ℝ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M)))
    (hfinite : ∀ s, Finite (GiantSignedCappedTrace H rows s))
    (value : (s : GiantSignedState PS PB M) → GiantSignedCappedTrace H rows s → A → Option ℕ) :
    giantSignedCappedTraceBoundaryPairing H ν rows (fun s t =>
      if MarkedPerformedInjective (value s t) then 1 else 0) =
      ∑ σ : Equiv.Perm A, ((σ.sign : ℤ) : ℂ) *
        giantSignedCappedTraceBoundaryPairing H ν rows (fun s t =>
          if MarkedBirthPermutationEvent (value s t) σ then 1 else 0) := by
  let s₀ (y : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) : GiantSignedState PS PB M :=
    (y,a,giantSignedEmptyMemory PB)
  let T := Σ y : GiantTwoSidedResidueState PS M, Σ a : MarkedPhysicalMarking PB M,
    GiantSignedCappedTrace H rows (s₀ y a)
  let _ : ∀ s, Fintype (GiantSignedCappedTrace H rows s) := fun s => @Fintype.ofFinite _ (hfinite s)
  let _ : Fintype T := by unfold T; infer_instance
  let w (t : T) :=
    ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν t.2.1 : ℝ) : ℂ) *
      giantSignedTraceWeight giantSignedBoundary rows (s₀ t.1 t.2.1) t.2.2.val
  let v (t : T) := value (s₀ t.1 t.2.1) t.2.2
  have hsum (p : (A → Option ℕ) → Prop) :
      giantSignedCappedTraceBoundaryPairing H ν rows (fun s t => if p (value s t) then 1 else 0) =
        ∑ t : T, if p (v t) then w t else 0 := by
    have hflat : giantSignedCappedTraceBoundaryPairing H ν rows (fun s t => if p (value s t) then 1 else 0) =
        ∑ t : T, w t * (if p (v t) then 1 else 0) := by
      unfold giantSignedCappedTraceBoundaryPairing
      simp only [T, Fintype.sum_sigma, tsum_fintype, w, v, s₀, Finset.mul_sum, mul_assoc]
    exact hflat.trans (Finset.sum_congr rfl (fun t _ => by split_ifs <;> simp only [mul_one, mul_zero]))
  refine (hsum MarkedPerformedInjective).trans ((markedBirthDistinct_weighted_permutation_sum v w).trans ?_)
  exact Finset.sum_congr rfl (fun σ _ =>
    congrArg (fun z => ((σ.sign : ℤ) : ℂ) * z) (hsum (fun p => MarkedBirthPermutationEvent p σ)).symm)

variable {I : Type u} [DecidableEq S] [DecidableEq B] {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η

def giantSignedTraceBirthDistinctIndicator (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace Rows s) : ℂ :=
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t
  if GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history) then 1 else 0

theorem giantSignedTraceBirthDistinctIndicator_norm_le (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace Rows s) :
    ‖giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K η s t‖ ≤ 1 := by
  unfold giantSignedTraceBirthDistinctIndicator
  dsimp only
  split_ifs <;> simp

def giantSignedCappedDistinctTraceBoundary (H : ℕ) : ℂ :=
    giantSignedGuardedTraceBoundaryPairing ν Rows (fun s t =>
      if GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) Rows s t then
        giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K η s t else 0)

def giantSignedCappedBirthPermutationSum (H : ℕ) : ℂ :=
  ∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
    ((σ.sign : ℤ) : ℂ) *
      giantSignedCappedBirthEventBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ

theorem giantSignedTraceBirthDistinctIndicator_eq_capped (H : ℕ)
    (s : GiantSignedState PS PB (k+ell)) (t : GiantSignedCappedTrace H Rows s) :
    giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K η s t.val =
      if MarkedPerformedInjective (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t)
        then 1 else 0 := by
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t.val
  let d := giantSignedChronologicalBirthData z.history
  have hH := giantSignedTraceChronology_batch_le ν V q ρ θ n patterns C κ visitQ ζ K η s t.val H t.property
  change (if GiantSignedBirthDistinct d then (1 : ℂ) else 0) =
    (if MarkedPerformedInjective (giantSignedUniformBirthValue d H hH) then 1 else 0)
  rw [giantSignedBirthDistinct_iff_uniform d H hH]

theorem giantSignedCappedTraceDistinctBoundary_permutation_sum (H : ℕ) :
    giantSignedCappedDistinctTraceBoundary ν V q ρ θ n patterns C κ visitQ ζ K η H =
      giantSignedCappedBirthPermutationSum ν V q ρ θ n patterns C κ visitQ ζ K η H := by
  let value := giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η
  have hfinite (s : GiantSignedState PS PB (k+ell)) : Finite (GiantSignedCappedTrace H Rows s) :=
    giantSignedChronologicalTraceWithin_finite ν V q ρ θ H n patterns C κ visitQ ζ K η s
  let F (s : GiantSignedState PS PB (k+ell)) (t : GiantSignedCappedTrace H Rows s) :=
    if MarkedPerformedInjective (value s t) then (1 : ℂ) else 0
  have hval := giantSignedTraceBirthDistinctIndicator_eq_capped ν V q ρ θ n patterns C κ visitQ ζ K η H
  calc
    _ = giantSignedCappedTraceBoundaryPairing H ν Rows (fun s t =>
        giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K η s t.val) :=
      (giantSignedCappedTraceBoundaryPairing_eq_guarded H ν Rows _).symm
    _ = giantSignedCappedTraceBoundaryPairing H ν Rows F :=
      congrArg (giantSignedCappedTraceBoundaryPairing H ν Rows) (funext (fun s => funext (hval s)))
    _ = _ := by
      refine (giantSignedCappedTraceBoundaryPairing_permutation_sum H ν Rows hfinite value).trans ?_
      unfold giantSignedCappedBirthPermutationSum
      let Perm := Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)
      exact Finset.sum_congr (congrArg (@Finset.univ Perm) (Subsingleton.elim _ _)) (fun _ _ => rfl)

end
end ArtinMatthews
