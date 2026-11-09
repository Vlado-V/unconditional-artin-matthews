module

public import ArtinMatthews.GiantSignedTraceBirthTotal
public import ArtinMatthews.GiantSignedTraceProjection


set_option backward.privateInPublic true
@[expose] public section

/-! A cutoff failure on the original dependent trace forces many actual
ghost births. Each edge can add only its selected store slots. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

theorem giantSignedChronologicalTraceWithin_of_births
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) (budget H n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s)
    (hb : (∑ g, s.2.2.1 g) +
      giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s t +
        (ell+budget)*Fintype.card B*n ≤ H) :
    GiantSignedTraceWithin (fun s => (∑ g, s.2.2.1 g) ≤ H)
      (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s t := by
  induction n generalizing s with
  | zero =>
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      change (Σ _ : GiantSignedGhostMemoryMoves s.2.2, PUnit) at t
      rcases t with ⟨r,z⟩
      have hg : (∑ g, (G.target s r).2.2.1 g) ≤
          (∑ g, s.2.2.1 g) + (∑ g, (r g).2.1) := giantSignedGhostTraceRow_degree_le ν _ _ _ s r
      change (∑ g, s.2.2.1 g) + (∑ g, (r g).2.1) + (ell+budget)*Fintype.card B*0 ≤ H at hb
      change (∑ g, s.2.2.1 g) ≤ H ∧ (∑ g, (G.target s r).2.2.1 g) ≤ H ∧ True
      exact ⟨by omega, by omega, trivial⟩
  | succ n ih =>
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let E := giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      let rest := giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ)
      change (Σ r : G.Move s, Σ e : E.Move (G.target s r),
        GiantSignedTrace rest (E.target (G.target s r) e)) at t
      rcases t with ⟨r,e,t⟩
      let y := G.target s r
      let z := E.target y e
      let birthTail := giantSignedChronologicalTraceBirthTotal ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ) z t
      have hg : (∑ g, y.2.2.1 g) ≤ (∑ g, s.2.2.1 g) + (∑ g, (r g).2.1) :=
        giantSignedGhostTraceRow_degree_le ν _ _ _ s r
      have he : (∑ g, z.2.2.1 g) ≤ (∑ g, y.2.2.1 g) + (ell+budget)*Fintype.card B :=
        giantSignedRawEdgeTarget_degree_le (κ 0) y e.2 budget (hC 0 e.1.val e.1.property)
      change (∑ g, s.2.2.1 g) + ((∑ g, (r g).2.1) + birthTail) +
        (ell+budget)*Fintype.card B*(n+1) ≤ H at hb
      rw [Nat.mul_succ] at hb
      have ht : (∑ g, z.2.2.1 g) + birthTail + (ell+budget)*Fintype.card B*n ≤ H := by omega
      have htail := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => hC i.succ)
        (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
        (fun i => η i.succ) z t ht
      change (∑ g, s.2.2.1 g) ≤ H ∧ (∑ g, y.2.2.1 g) ≤ H ∧
        (∑ g, y.2.2.1 g) ≤ H ∧ (∑ g, z.2.2.1 g) ≤ H ∧
        GiantSignedTraceWithin (fun s => (∑ g, s.2.2.1 g) ≤ H) rest z t
      exact ⟨by omega, by omega, by omega, by omega, htail⟩

theorem giantSignedChronologicalTrace_cap_failure_births
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) (budget H n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s)
    (hs : s.2.2 = giantSignedEmptyMemory PB)
    (hfail : ¬ GiantSignedTraceWithin (fun s => (∑ g, s.2.2.1 g) ≤ H)
      (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s t) :
    H < giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s t +
      (ell+budget)*Fintype.card B*n := by
  by_contra hb
  apply hfail
  apply giantSignedChronologicalTraceWithin_of_births ν V q ρ θ budget H n patterns C hC κ visitQ ζ K η s t
  have hz (g : B) : s.2.2.1 g = 0 := congrArg (fun m : GiantSignedMemory PB => m.1 g) hs
  simpa only [hz, Finset.sum_const_zero, zero_add] using Nat.le_of_not_gt hb

end
end ArtinMatthews
