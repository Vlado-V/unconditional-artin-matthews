module

public import ArtinMatthews.GiantSignedCappedBoundaryFourier
public import ArtinMatthews.GiantSignedCappedTraceFinite
public import ArtinMatthews.GiantSignedTraceBirthData


set_option backward.privateInPublic true
@[expose] public section

/-! The literal initial, ghost and edge multipliers give the circle
integral of the signed capped event, with every original pattern retained. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
local notation "Frame" => GiantSignedUniformBirthAddress B (k+ell) n H

def giantSignedCappedTraceBirthValue (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedCappedTrace H Rows s) : Frame → Option ℕ :=
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t.val
  giantSignedUniformBirthValue (giantSignedChronologicalBirthData z.history) H
    (giantSignedTraceChronology_batch_le ν V q ρ θ n patterns C κ visitQ ζ K η s t.val H t.property)

def giantSignedCappedBirthEventBoundary (σ : Equiv.Perm Frame) : ℂ :=
  giantSignedCappedTraceBoundaryPairing H ν Rows (fun s t =>
    if MarkedBirthPermutationEvent
      (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ then 1 else 0)

def giantSignedProjectedFrameBoundary (σ : Equiv.Perm Frame) (τ : Frame → AddCircle (1 : ℝ)) : ℂ :=
  giantSignedProjectedBirthBoundaryPairing H ν V q ρ θ n patterns C κ visitQ ζ K
    (fun i v s r => η i v s r * giantSignedRawEdgeFramePhase σ τ i s r)
    (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)

theorem giantSignedProjectedFrameBoundary_eq_trace
    (hr : ∀ r ∈ Rows, GiantSignedTraceRowAbsolute (fun s => ∑ g, s.2.2.1 g) r)
    (σ : Equiv.Perm Frame) (τ : Frame → AddCircle (1 : ℝ)) :
    giantSignedProjectedFrameBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ τ =
      giantSignedCappedTraceBoundaryPairing H ν Rows (fun s t =>
        giantSignedBirthPermutationPhase
          (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ τ) := by
  unfold giantSignedProjectedFrameBoundary giantSignedProjectedBirthBoundaryPairing giantSignedCappedTraceBoundaryPairing
  apply Finset.sum_congr rfl
  intro y _
  refine Finset.sum_congr (by ext a; simp) ?_
  intro a _
  let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
  let ψ (i : Fin n) (v : I) (z : GiantSignedState PS PB (k+ell))
      (r : GiantSignedRawEdgeMove PS PB ell (C i v) z.2.2) :=
    giantSignedRawEdgeFramePhase σ τ i z r
  let φ := giantSignedVisitFramePhase (PB := PB) σ τ
  let A := giantSignedInitialFramePhase σ τ a
  let mass := ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ)
  let G : Set (GiantSignedTrace Rows s) := {t | GiantSignedTraceWithin
    (fun x => (∑ g, x.2.2.1 g) ≤ H) Rows s t}
  let w := giantSignedTraceWeight giantSignedBoundary Rows s
  let F (t : G) := giantSignedBirthPermutationPhase
    (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ τ
  let j := giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ
  let r := giantSignedTraceMultipliersProduct Rows j s
  have hw := giantSignedProjectedBirthChronologicalWord_trace ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ
    H giantSignedBoundary giantSignedBoundary_exponential
    (fun i v _ z r => giantSignedRawEdgeFramePhase_norm_le σ τ i z r)
    (fun i b p => giantSignedFrameLocalMultiplier_norm_le σ τ (.visit i) _) hr s
  change mass * A * _ = mass * ∑' t : G, w t.val * F t
  refine (congrArg (fun v : ℂ => mass * A * v) hw).trans ?_
  change mass * A * (∑' t, if t ∈ G then w t * r t else 0) =
    mass * ∑' t : G, w t.val * F t
  rw [mul_assoc]
  apply congrArg (fun z => mass * z)
  rw [← tsum_mul_left]
  let v (t : GiantSignedTrace Rows s) := if ht : t ∈ G then w t * F ⟨t,ht⟩ else 0
  have hv : (∑' t : G, v t.val) = ∑' t : G, w t.val * F t :=
    tsum_congr (fun t => dite_eq_left t.property)
  refine Eq.trans ?_ ((tsum_subtype G v).symm.trans hv)
  apply tsum_congr
  intro t
  by_cases ht : t ∈ G
  · rw [ite_eq_left ht, Set.indicator_of_mem ht]
    dsimp only [v]
    rw [dite_eq_left ht]
    let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t
    let d := giantSignedChronologicalBirthData z.history
    have hH := giantSignedTraceChronology_batch_le ν V q ρ θ n patterns C κ visitQ ζ K η s t H ht
    have ha : d.initial = a := congrArg (fun z : GiantSignedState PS PB (k+ell) => z.2.1) z.first
    have hm := giantSignedTraceMultipliersProduct_birthData ν V q ρ θ n patterns C κ visitQ ζ K η s t
      (fun i _ target promoted => giantSignedEdgeFramePhase σ τ i target promoted) φ
    have hp := giantSignedFramePhaseProduct_eq d hH σ τ
    rw [ha] at hp
    have hF (inst : DecidableEq Frame) :
        @giantSignedBirthPermutationPhase Frame inferInstance inst (giantSignedUniformBirthValue d H hH) σ τ =
          F ⟨t,ht⟩ := by
      unfold F giantSignedCappedTraceBirthValue
      exact congrArg (fun e : DecidableEq Frame =>
        @giantSignedBirthPermutationPhase Frame inferInstance e (giantSignedUniformBirthValue d H hH) σ τ)
        (Subsingleton.elim _ _)
    calc
      A * (w t * r t) = w t * (A * r t) := by ring
      _ = w t * F ⟨t,ht⟩ :=
        congrArg (fun v => w t * v) ((congrArg (fun v => A * v) hm).trans (hp.trans (hF _)))
  · rw [ite_eq_right ht, Set.indicator_of_notMem ht, mul_zero]

theorem giantSignedCappedBirthEventBoundary_eq_integral
    (hr : ∀ r ∈ Rows, GiantSignedTraceRowAbsolute (fun s => ∑ g, s.2.2.1 g) r)
    (σ : Equiv.Perm Frame) :
    giantSignedCappedBirthEventBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ =
      ∫ τ : Frame → AddCircle (1 : ℝ),
        giantSignedProjectedFrameBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ τ
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
  have hfinite (s : GiantSignedState PS PB (k+ell)) : Finite (GiantSignedCappedTrace H Rows s) :=
    giantSignedChronologicalTraceWithin_finite ν V q ρ θ H n patterns C κ visitQ ζ K η s
  simp_rw [giantSignedProjectedFrameBoundary_eq_trace H ν V q ρ θ n patterns C κ visitQ ζ K η hr σ]
  exact (giantSignedCappedTraceBoundaryPairing_event_integral H ν Rows hfinite
    (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η) σ).symm

end
end ArtinMatthews
