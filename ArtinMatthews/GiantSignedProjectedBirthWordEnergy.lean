module

public import ArtinMatthews.GiantSignedProjectedBirthWord
public import ArtinMatthews.GiantSignedProjectedRawEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Energy follows the literal projected birth word with one factor per
visit and a separate factor for each actual edge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedProjectedBirthChronologicalWord_energy_of_local
    (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) (G : ℝ≥0∞)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ (n : ℕ) (patterns : Fin n → Finset I)
      (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
      (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
      (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
      (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ)
      (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB)
      (A : Fin n → ℝ≥0∞),
      (∀ i p, p ∈ patterns i → ∀ (s : GiantSignedState PS PB (k+ell))
        (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
        (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 σ)),
        η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
          η i p s (giantSignedRawEdgeOldEquiv s.2.2 σ r)) →
      (∀ (i : Fin (n+1)) (w : GiantSignedState PS PB (k+ell) → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
        let z := giantSignedProjectedBirthVisit H ν V (visitQ i) ρ (φ i) w
        (∀ s a, GiantSignedMemorySymmetric (fun m => z (s,a,m))) ∧
        giantSignedStateEnergy PS ν z ≤ G * giantSignedStateEnergy PS ν w) →
      (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
        giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
          (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i) w) ≤
          A i * giantSignedStateEnergy PS ν w) →
      let w := giantSignedProjectedBirthChronologicalWord H ν V q ρ θ f n
        patterns C κ visitQ ζ K η φ
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) ∧
      giantSignedStateEnergy PS ν w ≤ G ^ (n+1) * (∏ i, A i) * giantSignedStateEnergy PS ν f := by
  intro n
  induction n with
  | zero =>
      intro patterns C κ visitQ ζ K η φ A hη hvisit hedge
      simpa only [giantSignedProjectedBirthChronologicalWord, Nat.zero_add, pow_one,
        Fin.prod_univ_zero, mul_one] using hvisit 0 f hf
  | succ n ih =>
      intro patterns C κ visitQ ζ K η φ A hη hvisit hedge
      let tail := giantSignedProjectedBirthChronologicalWord H ν V q ρ θ f n
        (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
        (fun i => η i.succ) (fun i => φ i.succ)
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
        (fun i => η i.succ) (fun i => φ i.succ) (fun i => A i.succ)
        (fun i => hη i.succ) (fun i => hvisit i.succ) (fun i => hedge i.succ)
      let z := giantSignedProjectedRawEdgeFamilyApply H ν V (patterns 0) (C 0) (κ 0)
        q ρ θ (ζ 0) (K 0) (η 0) tail
      have hz : ∀ s a, GiantSignedMemorySymmetric (fun m => z (s,a,m)) :=
        giantSignedProjectedRawEdgeFamilyApply_symmetric_of_equivariant H ν V (patterns 0)
          (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0) (hη 0) tail ht.1
      refine ⟨(hvisit 0 z hz).1, ?_⟩
      calc
        _ ≤ G * giantSignedStateEnergy PS ν z := (hvisit 0 z hz).2
        _ ≤ G * (A 0 * giantSignedStateEnergy PS ν tail) :=
          mul_le_mul_right (hedge 0 tail ht.1) G
        _ ≤ G * (A 0 * (G ^ (n+1) * (∏ i : Fin n, A i.succ) * giantSignedStateEnergy PS ν f)) :=
          mul_le_mul_right (mul_le_mul_right ht.2 (A 0)) G
        _ = _ := by rw [Fin.prod_univ_succ, pow_succ G (n+1)]; ac_rfl

end
end ArtinMatthews
