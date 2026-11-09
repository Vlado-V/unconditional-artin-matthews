module

public import ArtinMatthews.GiantSignedRawEdgeData
public import ArtinMatthews.GiantSignedStateGhostGroup


set_option backward.privateInPublic true
@[expose] public section

/-! The original visit-edge word on the full signed state. Every finite
pattern sum is retained. The visits act at both endpoints of the word. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B I : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedChronologicalVisit {M : ℕ} (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (q ρ : ℝ) (f : GiantSignedState PS PB M → ℂ) :
    GiantSignedState PS PB M → ℂ :=
  giantSignedStateGhostGroup PS ν V q ρ f

def giantSignedChronologicalWord (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    (n : ℕ) → (patterns : Fin n → Finset I) →
      (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      ((i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      ((i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      GiantSignedState PS PB (k+ell) → ℂ
  | 0, _, _, _, visitQ, _, _, _ =>
      giantSignedChronologicalVisit ν V (visitQ 0) ρ f
  | n+1, patterns, C, κ, visitQ, ζ, K, η =>
      giantSignedChronologicalVisit ν V (visitQ 0) ρ
        (giantSignedRawEdgeFamilyApply ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
          (giantSignedChronologicalWord ν V q ρ θ f n
            (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
            (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)))

theorem giantSignedChronologicalWord_zero (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (patterns : Fin 0 → Finset I)
    (C : Fin 0 → I → B → Finset (Fin k)) (κ : Fin 0 → ℤ) (visitQ : Fin 1 → ℝ)
    (ζ : Fin 0 → ℝ) (K : (i : Fin 0) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin 0) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) :
    giantSignedChronologicalWord ν V q ρ θ f 0 patterns C κ visitQ ζ K η =
      giantSignedChronologicalVisit ν V (visitQ 0) ρ f := rfl

theorem giantSignedChronologicalWord_succ (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin (n+1) → Finset I) (C : Fin (n+1) → I → B → Finset (Fin k))
    (κ : Fin (n+1) → ℤ) (visitQ : Fin (n+2) → ℝ) (ζ : Fin (n+1) → ℝ)
    (K : (i : Fin (n+1)) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin (n+1)) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) :
    giantSignedChronologicalWord ν V q ρ θ f (n+1) patterns C κ visitQ ζ K η =
      giantSignedChronologicalVisit ν V (visitQ 0) ρ
        (giantSignedRawEdgeFamilyApply ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
          (giantSignedChronologicalWord ν V q ρ θ f n
            (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
            (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ))) := rfl

def giantSignedChronologicalBoundaryPairing (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (q ρ θ : ℝ) (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) : ℂ :=
  ∑ y : GiantTwoSidedResidueState PS (k+ell), ∑ a : MarkedPhysicalMarking PB (k+ell),
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ) *
      giantSignedChronologicalWord ν V q ρ θ giantSignedBoundary n patterns C κ visitQ ζ K η
        (y, a, giantSignedEmptyMemory PB)

end
end ArtinMatthews
