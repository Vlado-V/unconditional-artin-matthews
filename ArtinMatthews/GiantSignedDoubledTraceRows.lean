module

public import ArtinMatthews.GiantSignedTraceBirthScale
public import ArtinMatthews.GiantSignedTraceEdgeAbsolute
public import ArtinMatthews.GiantSignedDoubledChronologicalWord


set_option backward.privateInPublic true
@[expose] public section

/-! The doubled positive word changes the coefficients on the original
moves. All state transitions and endpoint choices remain literal. -/
namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

def giantSignedAbsoluteEdgeTraceRow (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ) :
    GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell)) :=
  giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K
    (fun v => giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ (K v) (η v))

theorem giantSignedAbsoluteEdgeTraceRow_coefficient (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ) (s : GiantSignedState PS PB (k+ell))
    (r : Σ v : patterns, GiantSignedRawEdgeMove PS PB ell (C v.val) s.2.2) :
    (giantSignedAbsoluteEdgeTraceRow ν V patterns C κ q ρ θ ζ K η).coefficient s r =
      (‖(giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η).coefficient s r‖ : ℂ) :=
  giantSignedRawEdgeAbsoluteMultiplier_coefficient ν V κ q ρ θ ζ (K r.1.val) (η r.1.val) s r.2

def giantSignedDoubledTraceRows (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      ((i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      ((i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell)))
  | 0, _, _, _, visitQ, _, _, _ => [giantSignedDoubledVisitTraceRow ν V (visitQ 0) ρ]
  | n+1, patterns, C, κ, visitQ, ζ, K, η =>
      giantSignedDoubledVisitTraceRow ν V (visitQ 0) ρ ::
        giantSignedAbsoluteEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0) ::
        giantSignedDoubledTraceRows ν V q ρ θ n (fun i => patterns i.succ)
          (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
          (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedDoubledTraceRows_word (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) :
    giantSignedTraceWord (giantSignedDoubledTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) f =
      giantSignedDoubledChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K
        (fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v)) := by
  induction n with
  | zero => exact giantSignedDoubledVisitTraceRow_apply ν V (visitQ 0) ρ f
  | succ n ih =>
      simp only [giantSignedDoubledTraceRows, giantSignedTraceWord, List.foldr_cons,
        giantSignedDoubledVisitTraceRow_apply, giantSignedAbsoluteEdgeTraceRow,
        giantSignedEdgeTraceRow_apply, giantSignedDoubledChronologicalWord]
      rw [← giantSignedTraceWord, ih]

end
end ArtinMatthews
