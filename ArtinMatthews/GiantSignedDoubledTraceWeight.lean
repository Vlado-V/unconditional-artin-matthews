module

public import ArtinMatthews.GiantSignedDoubledTraceEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! The exact total birth exponent multiplies the norm of the full
original trace coefficient, including the original terminal test. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

theorem giantSignedDoubledTraceWeight_eq (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (q ρ θ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s) :
    giantSignedTraceWeight (fun s => (‖f s‖ : ℂ))
      (giantSignedDoubledTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s
      (giantSignedDoubledTraceEquiv ν V q ρ θ n patterns C κ visitQ ζ K η s t) =
      (2:ℂ)^giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s t *
        (‖giantSignedTraceWeight f
          (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s t‖ : ℂ) := by
  induction n generalizing s with
  | zero =>
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let G' := giantSignedDoubledVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      change (Σ _ : GiantSignedGhostMemoryMoves s.2.2, PUnit) at t
      rcases t with ⟨r,_⟩
      have hG : G'.coefficient s r = (2:ℂ)^(∑ g, (r g).2.1) * (‖G.coefficient s r‖ : ℂ) :=
        giantSignedDoubledVisitTraceRow_coefficient ν hν V (visitQ 0) ρ s r
      change G'.coefficient s r * (‖f (G.target s r)‖ : ℂ) =
        (2:ℂ)^(∑ g, (r g).2.1) * (‖G.coefficient s r * f (G.target s r)‖ : ℂ)
      rw [hG, norm_mul, Complex.ofReal_mul, mul_assoc]
  | succ n ih =>
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let G' := giantSignedDoubledVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let E := giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      let E' := giantSignedAbsoluteEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      let rest := giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ)
      change (Σ r : G.Move s, Σ e : E.Move (G.target s r),
        GiantSignedTrace rest (E.target (G.target s r) e)) at t
      rcases t with ⟨r,e,t⟩
      let y := G.target s r
      let z := E.target y e
      have hG : G'.coefficient s r = (2:ℂ)^(∑ g, (r g).2.1) * (‖G.coefficient s r‖ : ℂ) :=
        giantSignedDoubledVisitTraceRow_coefficient ν hν V (visitQ 0) ρ s r
      have hE : E'.coefficient y e = (‖E.coefficient y e‖ : ℂ) :=
        giantSignedAbsoluteEdgeTraceRow_coefficient ν V (patterns 0) (C 0)
          (κ 0) q ρ θ (ζ 0) (K 0) (η 0) y e
      let rest' := giantSignedDoubledTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ)
      let eTail := giantSignedDoubledTraceEquiv ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ) z
      let bTail := giantSignedChronologicalTraceBirthTotal ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ) z t
      have htail : giantSignedTraceWeight (fun s => (‖f s‖ : ℂ)) rest' z (eTail t) =
          (2:ℂ)^bTail * (‖giantSignedTraceWeight f rest z t‖ : ℂ) :=
        ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
          (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
          (fun i => η i.succ) z t
      change G'.coefficient s r *
          (E'.coefficient y e * giantSignedTraceWeight (fun s => (‖f s‖ : ℂ)) rest' z (eTail t)) =
        (2:ℂ)^((∑ g, (r g).2.1)+bTail) *
          (‖G.coefficient s r * (E.coefficient y e * giantSignedTraceWeight f rest z t)‖ : ℂ)
      rw [hG, hE, htail, pow_add]
      simp only [norm_mul, Complex.ofReal_mul]
      ring

end
end ArtinMatthews
