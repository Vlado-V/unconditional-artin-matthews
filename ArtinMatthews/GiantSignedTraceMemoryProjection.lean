module

public import ArtinMatthews.GiantSignedTraceProjection
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedWordDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The original memory cutoff on each operation is the degree guard
on the very same dependent chronological trace. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell M : ℕ}

theorem giantSignedTraceProject_memory (H : ℕ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedTraceProject (fun s => (∑ g, s.2.2.1 g) ≤ H) f =
      giantSignedStateMemoryCutoff H f := by
  funext s
  by_cases hs : (∑ g, s.2.2.1 g) ≤ H <;>
    simp [giantSignedTraceProject, giantSignedStateMemoryCutoff, hs]

theorem giantSignedVisitTraceRow_projected (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (q ρ : ℝ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedTraceProjectedRowApply (fun s => (∑ g, s.2.2.1 g) ≤ H)
        (giantSignedVisitTraceRow ν V q ρ) f = giantSignedProjectedVisit H ν V q ρ f := by
  simp only [giantSignedTraceProjectedRowApply, giantSignedTraceProject_memory,
    giantSignedVisitTraceRow_apply, giantSignedProjectedVisit]

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedEdgeTraceRow_projected (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedTraceProjectedRowApply (fun s => (∑ g, s.2.2.1 g) ≤ H)
        (giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η) f =
      giantSignedProjectedRawEdgeFamilyApply H ν V patterns C κ q ρ θ ζ K η f := by
  simp only [giantSignedTraceProjectedRowApply, giantSignedTraceProject_memory,
    giantSignedEdgeTraceRow_apply, giantSignedProjectedRawEdgeFamilyApply]

theorem giantSignedChronologicalTraceRows_projected (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) :
    giantSignedTraceProjectedWord (fun s => (∑ g, s.2.2.1 g) ≤ H)
        (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) f =
      giantSignedProjectedChronologicalWord H ν V q ρ θ f n patterns C κ visitQ ζ K η := by
  induction n with
  | zero => exact giantSignedVisitTraceRow_projected H ν V (visitQ 0) ρ f
  | succ n ih =>
      simp only [giantSignedChronologicalTraceRows, giantSignedTraceProjectedWord, List.foldr_cons,
        giantSignedVisitTraceRow_projected, giantSignedEdgeTraceRow_projected,
        giantSignedProjectedChronologicalWord]
      rw [← giantSignedTraceProjectedWord, ih]

theorem giantSignedProjectedChronologicalWord_trace (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hr : ∀ r ∈ giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η,
      GiantSignedTraceRowAbsolute (fun s => ∑ g, s.2.2.1 g) r)
    (s : GiantSignedState PS PB (k+ell)) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    giantSignedProjectedChronologicalWord H ν V q ρ θ f n patterns C κ visitQ ζ K η s =
      ∑' t : GiantSignedTrace rows s,
        if GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t then
          giantSignedTraceWeight f rows s t else 0 := by
  dsimp only
  rw [← giantSignedChronologicalTraceRows_projected]
  let degree : GiantSignedState PS PB (k+ell) → ℕ := fun x => ∑ g, x.2.2.1 g
  have hExp : GiantSignedTraceExponential degree (fun x => ‖f x‖) := hf
  exact giantSignedTraceProjectedWord_eq degree f hExp _ hr _ s

end
end ArtinMatthews
