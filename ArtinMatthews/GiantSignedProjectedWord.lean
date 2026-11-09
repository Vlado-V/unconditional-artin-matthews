module

public import ArtinMatthews.GiantSignedChronologicalWord
public import ArtinMatthews.GiantSignedStateMemoryCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Each local operation is truncated on the original full state carrier.
The endpoint masses and all original edge data are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B I : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedProjectedVisit {M : ℕ} (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) : GiantSignedState PS PB M → ℂ :=
  giantSignedStateMemoryCutoff N
    (giantSignedChronologicalVisit ν V q ρ (giantSignedStateMemoryCutoff N f))

def giantSignedProjectedRawEdgeFamilyApply (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) : GiantSignedState PS PB (k+ell) → ℂ :=
  giantSignedStateMemoryCutoff N
    (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η
      (giantSignedStateMemoryCutoff N f))

def giantSignedProjectedChronologicalWord (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    (n : ℕ) → (patterns : Fin n → Finset I) →
      (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      ((i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      ((i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      GiantSignedState PS PB (k+ell) → ℂ
  | 0, _, _, _, visitQ, _, _, _ =>
      giantSignedProjectedVisit N ν V (visitQ 0) ρ f
  | n+1, patterns, C, κ, visitQ, ζ, K, η =>
      giantSignedProjectedVisit N ν V (visitQ 0) ρ
        (giantSignedProjectedRawEdgeFamilyApply N ν V (patterns 0) (C 0)
          (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
          (giantSignedProjectedChronologicalWord N ν V q ρ θ f n
            (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
            (fun i => visitQ i.succ) (fun i => ζ i.succ)
            (fun i => K i.succ) (fun i => η i.succ)))

def giantSignedProjectedChronologicalBoundaryPairing (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) : ℂ :=
  ∑ y : GiantTwoSidedResidueState PS (k+ell), ∑ a : MarkedPhysicalMarking PB (k+ell),
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ) *
      giantSignedProjectedChronologicalWord N ν V q ρ θ giantSignedBoundary
        n patterns C κ visitQ ζ K η (y, a, giantSignedEmptyMemory PB)

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedProjectedVisit_outside {M : ℕ} (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) (s : GiantSignedState PS PB M)
    (hs : N < ∑ g, s.2.2.1 g) :
    giantSignedProjectedVisit N ν V q ρ f s = 0 :=
  giantSignedStateMemoryCutoff_of_lt N _ s hs

theorem giantSignedProjectedRawEdgeFamilyApply_outside (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell))
    (hs : N < ∑ g, s.2.2.1 g) :
    giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η f s = 0 :=
  giantSignedStateMemoryCutoff_of_lt N _ s hs

theorem giantSignedProjectedChronologicalWord_outside (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) (hs : N < ∑ g, s.2.2.1 g) :
    giantSignedProjectedChronologicalWord N ν V q ρ θ f
      n patterns C κ visitQ ζ K η s = 0 := by
  cases n <;> exact giantSignedProjectedVisit_outside N ν V _ ρ _ s hs

end
end ArtinMatthews
