module

public import ArtinMatthews.GiantSignedProjectedVisitEnergy
public import ArtinMatthews.GiantSignedProjectedRawEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Energy iteration follows the literal chronological recursion.
There are n edges and n+1 visits, including both endpoint visits. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedProjectedChronologicalWord_energy_of_local
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (q ρ θ : ℝ) (G A : ℝ≥0∞)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ (n : ℕ) (patterns : Fin n → Finset I)
      (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
      (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
      (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
      (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ),
      (∀ i p, p ∈ patterns i → ∀ (s : GiantSignedState PS PB (k+ell))
        (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
        (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 σ)),
        η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
          η i p s (giantSignedRawEdgeOldEquiv s.2.2 σ r)) →
      (∀ (i : Fin (n+1)) (w : GiantSignedState PS PB (k+ell) → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
        giantSignedStateEnergy PS ν (giantSignedProjectedVisit N ν V (visitQ i) ρ w) ≤
          G * giantSignedStateEnergy PS ν w) →
      (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
        giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply N ν V
          (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i) w) ≤
          A * giantSignedStateEnergy PS ν w) →
      (∀ s a, GiantSignedMemorySymmetric (fun m =>
        giantSignedProjectedChronologicalWord N ν V q ρ θ f n patterns C κ visitQ ζ K η (s,a,m))) ∧
      giantSignedStateEnergy PS ν
        (giantSignedProjectedChronologicalWord N ν V q ρ θ f n patterns C κ visitQ ζ K η) ≤
          G ^ (n+1) * A ^ n * giantSignedStateEnergy PS ν f := by
  intro n
  induction n with
  | zero =>
      intro patterns C κ visitQ ζ K η hη hvisit hedge
      refine ⟨giantSignedProjectedVisit_memorySymmetric N ν hν V (visitQ 0) ρ f hf, ?_⟩
      simpa only [giantSignedProjectedChronologicalWord, Nat.zero_add, pow_zero, pow_one, mul_one]
        using hvisit 0 f hf
  | succ n ih =>
      intro patterns C κ visitQ ζ K η hη hvisit hedge
      let tail := giantSignedProjectedChronologicalWord N ν V q ρ θ f n
        (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        (fun i => hη i.succ) (fun i => hvisit i.succ) (fun i => hedge i.succ)
      let w := giantSignedProjectedRawEdgeFamilyApply N ν V (patterns 0) (C 0) (κ 0)
        q ρ θ (ζ 0) (K 0) (η 0) tail
      have hw : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m)) :=
        giantSignedProjectedRawEdgeFamilyApply_symmetric_of_equivariant N ν V (patterns 0)
          (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0) (hη 0) tail ht.1
      refine ⟨giantSignedProjectedVisit_memorySymmetric N ν hν V (visitQ 0) ρ w hw, ?_⟩
      calc
        _ ≤ G * giantSignedStateEnergy PS ν w := hvisit 0 w hw
        _ ≤ G * (A * giantSignedStateEnergy PS ν tail) :=
          mul_le_mul_right (hedge 0 tail ht.1) G
        _ ≤ G * (A * (G ^ (n+1) * A ^ n * giantSignedStateEnergy PS ν f)) :=
          mul_le_mul_right (mul_le_mul_right ht.2 A) G
        _ = _ := by rw [pow_succ G (n+1), pow_succ A n]; ac_rfl

end
end ArtinMatthews
