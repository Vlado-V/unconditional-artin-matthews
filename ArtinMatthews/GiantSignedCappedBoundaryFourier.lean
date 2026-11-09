module

public import ArtinMatthews.GiantSignedTraceBoundaryTail
public import ArtinMatthews.GiantSignedFramePhaseProduct


set_option backward.privateInPublic true
@[expose] public section

/-! Finite circle integration on the actual capped trace carrier. The
weight remains the original signed boundary coefficient. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B : Type u} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)]

abbrev GiantSignedCappedTrace (H : ℕ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M)))
    (s : GiantSignedState PS PB M) :=
  {t : GiantSignedTrace rows s //
    GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t}

def giantSignedCappedTraceBoundaryPairing (H : ℕ) (ν : ∀ g, PB g → ℝ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M)))
    (φ : (s : GiantSignedState PS PB M) → GiantSignedCappedTrace H rows s → ℂ) : ℂ :=
  ∑ y : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
    let s : GiantSignedState PS PB M := (y,a,giantSignedEmptyMemory PB)
    ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a : ℝ) : ℂ) *
      ∑' t : GiantSignedCappedTrace H rows s, giantSignedTraceWeight giantSignedBoundary rows s t.val * φ s t

theorem giantSignedCappedTraceBoundaryPairing_eq_guarded [DecidableEq S] [DecidableEq B]
    {k ell : ℕ} [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (H : ℕ) (ν : ∀ g, PB g → ℝ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell))))
    (φ : (s : GiantSignedState PS PB (k+ell)) → GiantSignedTrace rows s → ℂ) :
    giantSignedCappedTraceBoundaryPairing H ν rows (fun s t => φ s t.val) =
      giantSignedGuardedTraceBoundaryPairing ν rows (fun s t =>
        if GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t then φ s t else 0) := by
  unfold giantSignedCappedTraceBoundaryPairing giantSignedGuardedTraceBoundaryPairing
  apply Finset.sum_congr rfl
  intro y _
  refine Finset.sum_congr (by ext a; simp only [Finset.mem_univ]) ?_
  intro a _
  let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
  let G : Set (GiantSignedTrace rows s) := {t |
    GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t}
  let mass := ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ)
  change mass * (∑' t : G, giantSignedTraceWeight giantSignedBoundary rows s t.val * φ s t.val) =
    mass * ∑' t : GiantSignedTrace rows s,
      giantSignedTraceWeight giantSignedBoundary rows s t * (if t ∈ G then φ s t else 0)
  apply congrArg (fun z => mass * z)
  let f (t : GiantSignedTrace rows s) := giantSignedTraceWeight giantSignedBoundary rows s t * φ s t
  refine (tsum_subtype G f).trans ?_
  exact tsum_congr (fun t => by
    by_cases h : t ∈ G
    · rw [Set.indicator_of_mem h, ite_eq_left h]
    · rw [Set.indicator_of_notMem h, ite_eq_right h, mul_zero])

private theorem giantSignedCappedTrace_integral_sum {A T : Type*} [Fintype A] [DecidableEq A] [Fintype T]
    (w : T → ℂ) (v : T → A → Option ℕ) (σ : Equiv.Perm A) :
    (∫ θ : A → AddCircle (1 : ℝ), ∑ t, w t * giantSignedBirthPermutationPhase (v t) σ θ
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ∑ t, if MarkedBirthPermutationEvent (v t) σ then w t else 0 := by
  rw [integral_finsetSum _ (fun t _ => (giantSignedBirthPermutationPhase_integrable (v t) σ).const_mul (w t))]
  exact Finset.sum_congr rfl (fun t _ => by
    rw [integral_const_mul, giantSignedBirthPermutationPhase_integral]
    split_ifs <;> simp only [mul_one, mul_zero])

theorem giantSignedCappedTraceBoundaryPairing_event_integral {A : Type*} [Fintype A] [DecidableEq A]
    (H : ℕ) (ν : ∀ g, PB g → ℝ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M)))
    (hfinite : ∀ s, Finite (GiantSignedCappedTrace H rows s))
    (value : (s : GiantSignedState PS PB M) → GiantSignedCappedTrace H rows s → A → Option ℕ)
    (σ : Equiv.Perm A) :
    (∫ θ : A → AddCircle (1 : ℝ),
      giantSignedCappedTraceBoundaryPairing H ν rows
        (fun s t => giantSignedBirthPermutationPhase (value s t) σ θ)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      giantSignedCappedTraceBoundaryPairing H ν rows (fun s t =>
        if MarkedBirthPermutationEvent (value s t) σ then 1 else 0) := by
  let s₀ (y : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) : GiantSignedState PS PB M :=
    (y,a,giantSignedEmptyMemory PB)
  let T := Σ y : GiantTwoSidedResidueState PS M, Σ a : MarkedPhysicalMarking PB M,
    GiantSignedCappedTrace H rows (s₀ y a)
  let _ : ∀ s, Fintype (GiantSignedCappedTrace H rows s) := fun s =>
    @Fintype.ofFinite _ (hfinite s)
  let _ : Fintype T := by unfold T; infer_instance
  let w (t : T) :=
    ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν t.2.1 : ℝ) : ℂ) *
      giantSignedTraceWeight giantSignedBoundary rows (s₀ t.1 t.2.1) t.2.2.val
  let v (t : T) := value (s₀ t.1 t.2.1) t.2.2
  have hsum (f : (A → Option ℕ) → ℂ) :
      giantSignedCappedTraceBoundaryPairing H ν rows (fun s t => f (value s t)) =
        ∑ t : T, w t * f (v t) := by
    unfold giantSignedCappedTraceBoundaryPairing
    simp only [T, Fintype.sum_sigma, tsum_fintype, w, v, s₀, Finset.mul_sum, mul_assoc]
  have hp (θ : A → AddCircle (1 : ℝ)) :=
    hsum (fun p => giantSignedBirthPermutationPhase p σ θ)
  have he := hsum (fun p => if MarkedBirthPermutationEvent p σ then 1 else 0)
  refine (integral_congr_ae (Filter.Eventually.of_forall hp)).trans
    ((giantSignedCappedTrace_integral_sum w v σ).trans ?_)
  exact (Finset.sum_congr rfl (fun t _ => by split_ifs <;> simp only [mul_one, mul_zero])).trans he.symm

end
end ArtinMatthews
