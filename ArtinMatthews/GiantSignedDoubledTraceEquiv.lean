module

public import ArtinMatthews.GiantSignedDoubledTraceRows
public import ArtinMatthews.GiantSignedTraceBirthTotal


set_option backward.privateInPublic true
@[expose] public section

/-! Each doubled move has exactly the same target and choice data as
the original move. The dependent trace equivalence preserves all choices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

def giantSignedDoubledTraceEquiv (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s ≃
        GiantSignedTrace (giantSignedDoubledTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s
  | 0, _, _, _, _, _, _, _, _ => Equiv.refl _
  | n+1, patterns, C, κ, visitQ, ζ, K, η, s => by
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let E := giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      exact Equiv.sigmaCongrRight (fun r : G.Move s =>
        Equiv.sigmaCongrRight (fun e : E.Move (G.target s r) =>
          giantSignedDoubledTraceEquiv ν V q ρ θ n (fun i => patterns i.succ)
            (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
            (fun i => K i.succ) (fun i => η i.succ) (E.target (G.target s r) e)))

end
end ArtinMatthews
