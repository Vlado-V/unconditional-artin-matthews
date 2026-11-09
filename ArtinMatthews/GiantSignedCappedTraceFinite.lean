module

public import ArtinMatthews.GiantSignedTraceFinite
public import ArtinMatthews.GiantSignedTraceRows


set_option backward.privateInPublic true
@[expose] public section

/-! On a capped visit, every actual appended batch fits inside the
output degree. This proves finiteness of the same guarded trace. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M k ell : ℕ}

theorem giantSignedGhostTraceCappedMoves_finite (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (s : GiantSignedState PS PB M) (H : ℕ) :
    Finite {r : (giantSignedGhostTraceRow ν A C D).Move s //
      (∑ g, ((giantSignedGhostTraceRow ν A C D).target s r).2.2.1 g) ≤ H} := by
  classical
  let G := giantSignedGhostTraceRow (PS := PS) (M := M) ν A C D
  let U := {r : G.Move s // (∑ g, (G.target s r).2.2.1 g) ≤ H}
  let X := (g : B) → Finset (Fin (s.2.2.1 g)) × (Σ b : Fin (H+1), Fin b.val → PB g)
  letI : Fintype X := by dsimp only [X]; infer_instance
  have hb (r : U) (g : B) : (r.val g).2.1 ≤ H := by
    have ht : (r.val g).2.1 ≤ (G.target s r.val).2.2.1 g := by
      change (r.val g).2.1 ≤ ((r.val g).1ᶜ).card + (r.val g).2.1
      exact Nat.le_add_left _ _
    exact ht.trans ((Finset.single_le_sum (f := fun j => (G.target s r.val).2.2.1 j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans r.property)
  let encode (r : U) : X := fun g =>
    ((r.val g).1, ⟨⟨(r.val g).2.1, Nat.lt_succ_of_le (hb r g)⟩, (r.val g).2.2⟩)
  let decode (r : X) : G.Move s := fun g => ⟨(r g).1, (r g).2.1.val, (r g).2.2⟩
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  have he (r : U) : decode (encode r) = r.val := by
    funext g
    change (⟨(r.val g).1, (r.val g).2.1, (r.val g).2.2⟩ : GiantSignedGhostMoves
      (giantSignedMemoryGroupEquiv PB s.2.2 g)) = r.val g
    rcases r.val g with ⟨R,k,b⟩
    rfl
  exact (he a).symm.trans ((congrArg decode h).trans (he b))

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedChronologicalTraceWithin_finite
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) (H n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    Finite {t : GiantSignedTrace rows s //
      GiantSignedTraceWithin (fun z => (∑ g, z.2.2.1 g) ≤ H) rows s t} := by
  classical
  dsimp only
  apply giantSignedTraceWithin_finite
  clear s
  induction n with
  | zero =>
      intro r hr s
      change r ∈ [giantSignedVisitTraceRow ν V (visitQ 0) ρ] at hr
      rcases List.mem_singleton.mp hr with rfl
      exact giantSignedGhostTraceCappedMoves_finite ν _ _ _ s H
  | succ n ih =>
      intro r hr s
      simp only [giantSignedChronologicalTraceRows, List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact giantSignedGhostTraceCappedMoves_finite ν _ _ _ s H
      · let T := Σ v : patterns 0, GiantSignedRawEdgeMove PS PB ell (C 0 v.val) s.2.2
        let _ : Fintype T := by unfold T; infer_instance
        have hfinite : Finite T := inferInstance
        exact @Finite.of_injective _ T hfinite Subtype.val Subtype.val_injective
      · exact ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
          (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ) r hr s

end
end ArtinMatthews
