module

public import ArtinMatthews.GiantSignedTraceChronologySupport


set_option backward.privateInPublic true
@[expose] public section

/-! Replay a compatible chronology on the actual dependent row trace.
The target equality transports only the next state's dependent move type. -/

namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

def giantSignedChronologicalTail {n : ℕ} {C : Fin (n+1) → B → Finset (Fin k)}
    {batch : Fin (n+2) → B → ℕ} (h : GiantSignedChronologicalChoices PS PB ell C batch) :
    GiantSignedChronologicalChoices PS PB ell (fun i => C i.succ) (fun i => batch i.succ) where
  state i := h.state i.succ
  deleted i := h.deleted i.succ
  born i := h.born i.succ
  sourceSmallPermutation i := h.sourceSmallPermutation i.succ
  targetSmallPermutation i := h.targetSmallPermutation i.succ
  sourceBigPermutation i := h.sourceBigPermutation i.succ
  targetBigPermutation i := h.targetBigPermutation i.succ
  auxiliary i := h.auxiliary i.succ
  edge i := h.edge i.succ

theorem giantSignedChronologicalTail_compatible {n : ℕ} {C : Fin (n+1) → B → Finset (Fin k)}
    {batch : Fin (n+2) → B → ℕ} (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (κ : Fin (n+1) → ℤ) (hc : GiantSignedChronologicalCompatible κ h) :
    GiantSignedChronologicalCompatible (fun i => κ i.succ) (giantSignedChronologicalTail h) :=
  fun i => hc i.succ

local notation "One" => fun _ _ _ _ => (1 : ℂ)

def giantSignedTraceOfChronology (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
    (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
    (p : (i : Fin n) → patterns i) → (batch : Fin (n+1) → B → ℕ) →
    (h : GiantSignedChronologicalChoices PS PB ell (fun i => C i (p i).val) batch) →
    GiantSignedChronologicalCompatible κ h →
    GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One) (h.state 0)
  | 0, _, _, _, _, _, _, _, batch, h, _ =>
      ⟨giantSignedFixedGhostMove (h.state 0).2.2 (batch 0) (h.deleted 0) (h.born 0),PUnit.unit⟩
  | n+1, patterns, C, κ, visitQ, ζ, K, p, batch, h, hc => by
      let r := giantSignedFixedGhostMove (h.state 0).2.2 (batch 0) (h.deleted 0) (h.born 0)
      let a := giantSignedChronologicalAfterVisitState h (0 : Fin (n+1)).castSucc
      let move := giantSignedChronologicalRawMove h (0 : Fin (n+1))
      let e : Σ v : patterns 0, GiantSignedRawEdgeMove PS PB ell (C 0 v.val) a.2.2 := ⟨p 0,move⟩
      let rest := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) One
      let tail := giantSignedTraceOfChronology ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => p i.succ) (fun i => batch i.succ) (giantSignedChronologicalTail h)
        (giantSignedChronologicalTail_compatible h κ hc)
      have he : giantSignedRawEdgeTarget (κ 0) a move = h.state (0 : Fin (n+1)).succ :=
        giantSignedChronologicalRawMove_target κ h hc 0
      exact ⟨r,e,cast (congrArg (GiantSignedTrace rest) he.symm)
        (tail : GiantSignedTrace rest (h.state (0 : Fin (n+1)).succ))⟩

end
end ArtinMatthews
