module

public import ArtinMatthews.GiantSignedChronologicalMemo
public import ArtinMatthews.GiantSignedBirthTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Local tests verify the retained memo sequence on the actual moves. -/
namespace ArtinMatthews
noncomputable section

universe u
variable {S B I M : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (G : (i : Fin (n+1)) →
      GiantSignedTraceMemoRule M (giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ i) ρ))
    (E : (i : Fin n) →
      GiantSignedTraceMemoRule M (giantSignedEdgeTraceRow ν V (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i)))
    (μG : Fin (n+1) → M) (μE : Fin n → M)
    (ψ : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB)

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
local notation "Rules" => giantSignedChronologicalMemoRules ν V q ρ θ n patterns C κ visitQ ζ K η G E

theorem giantSignedChronologicalMemoAccept_of_product_ne_zero
    (hG : ∀ i (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedGhostMemoryMoves s.2.2),
      φ i (fun g => (r g).2.1) (fun g => (r g).2.2) ≠ 0 → (G i).accept (μG i) s r)
    (hGE : ∀ i (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedGhostMemoryMoves s.2.2),
      φ i.castSucc (fun g => (r g).2.1) (fun g => (r g).2.2) ≠ 0 →
      (G i.castSucc).update (μG i.castSucc) s r = μE i)
    (hE : ∀ i (s : GiantSignedState PS PB (k+ell))
      (r : Σ v : patterns i, GiantSignedRawEdgeMove PS PB ell (C i v.val) s.2.2),
      ψ i r.1.val s r.2 ≠ 0 →
      (E i).accept (μE i) s r ∧ (E i).update (μE i) s r = μG i.succ)
    (s : GiantSignedState PS PB (k+ell)) (t : GiantSignedTrace Rows s)
    (ht : giantSignedTraceMultipliersProduct Rows
      (giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ) s t ≠ 0) :
    GiantSignedTraceMemoAccept Rows Rules (μG 0) s t := by
  induction n generalizing s with
  | zero =>
      obtain ⟨r,t⟩ := t
      change φ 0 (fun g => (r g).2.1) (fun g => (r g).2.2) * 1 ≠ 0 at ht
      exact ⟨hG 0 s r (mul_ne_zero_iff.mp ht).1,trivial⟩
  | succ n ih =>
      obtain ⟨r,e,t⟩ := t
      let s' := (giantSignedVisitTraceRow ν V (visitQ 0) ρ).target s r
      let s'' := (giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)).target s' e
      let rows := giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
      let F := giantSignedChronologicalTraceMultipliers ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        (fun i => ψ i.succ) (fun i => φ i.succ)
      change φ 0 (fun g => (r g).2.1) (fun g => (r g).2.2) *
        (ψ 0 e.1.val s' e.2 * giantSignedTraceMultipliersProduct rows F s'' t) ≠ 0 at ht
      obtain ⟨hg,hRest⟩ := mul_ne_zero_iff.mp ht
      obtain ⟨he,hr⟩ := mul_ne_zero_iff.mp hRest
      have hV := hGE 0 s r hg
      have hE₀ := hE 0 s' e he
      have htail := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        (fun i => G i.succ) (fun i => E i.succ) (fun i => μG i.succ) (fun i => μE i.succ)
        (fun i => ψ i.succ) (fun i => φ i.succ) (fun i => hG i.succ) (fun i => hGE i.succ)
        (fun i => hE i.succ) s'' t hr
      refine ⟨hG 0 s r hg,?_⟩
      let rules := giantSignedChronologicalMemoRules ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        (fun i => G i.succ) (fun i => E i.succ)
      change (E 0).accept ((G 0).update (μG 0) s r) s' e ∧
        GiantSignedTraceMemoAccept rows rules ((E 0).update ((G 0).update (μG 0) s r) s' e) s'' t
      rw [show (G 0).update (μG 0) s r = μE 0 from hV, hE₀.2]
      exact ⟨hE₀.1,htail⟩

end
end ArtinMatthews
