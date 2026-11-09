module

public import ArtinMatthews.GiantSignedRawEdgeSplit
public import ArtinMatthews.GiantSignedSmallRareTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! Nonzero original store/promote terms force the corresponding rare gate.
The two endpoint products and all original ban conditions are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}

def giantSignedRawSourceBigProduct (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℕ :=
  giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
    giantTwoSidedPatternAuxiliaryProduct r.auxiliary

def giantSignedRawTargetBigProduct {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) : ℕ :=
  giantTwoSidedPatternCopiedProduct C r.bigTarget * giantTwoSidedPatternAuxiliaryProduct r.auxiliary

def GiantSignedRawSourceRareGate (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : Prop :=
  GiantSignedSmallSourceMemoryAllows s.1.val.2 κ (giantSignedRawSourceBigProduct s r)
    s.2.2 r.sourceSmallPermutation

def GiantSignedRawTargetRareGate (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : Prop :=
  GiantSignedSmallSourceMemoryAllows (giantSignedRawEdgeTarget κ s r).1.val.2 (-κ)
    (giantSignedRawTargetBigProduct r) (giantSignedRawEdgeTarget κ s r).2.2
    r.targetSmallPermutation

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawEdgeProduct_source_factor (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    giantSignedRawEdgeProduct s r =
      giantSignedSmallPermutationCopiedProduct s.1.val.2 r.sourceSmallPermutation *
        giantSignedRawSourceBigProduct s r := rfl

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawEdgeProduct_target_factor (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeCondition κ s r) :
    giantSignedRawEdgeProduct s r =
      giantSignedSmallPermutationCopiedProduct (giantSignedRawEdgeTarget κ s r).1.val.2
        r.targetSmallPermutation * giantSignedRawTargetBigProduct r := by
  have hsmall : giantSignedSmallPermutationCopiedProduct
      (giantSignedRawEdgeTarget κ s r).1.val.2 r.targetSmallPermutation =
      ∏ g : S, ∏ i : Fin k, (r.smallTarget.val.2 g (Fin.castAdd ell i)).val := by
    change (∏ g : S, ∏ i : Fin k,
      ((giantTwoSidedResiduePermute r.targetSmallPermutation
        ((giantTwoSidedResiduePermute r.targetSmallPermutation).symm r.smallTarget)).val.2
          g (Fin.castAdd ell i)).val) = _
    rw [Equiv.apply_symm_apply]
  rw [hsmall]
  unfold giantSignedRawEdgeProduct giantSignedRawTargetBigProduct
  rw [giantTwoSidedPatternCopiedProduct_eq hr.2.2.1]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg Subtype.val (hr.1 g i).symm

theorem giantSignedRawEdgeCoefficient_conditions
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hne : giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r ≠ 0) :
    GiantSignedRawEdgeCondition κ s r ∧
      GiantSignedEdgeHits (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
        (giantSignedPatternFreeLabels C r.bigTarget) r.choice ∧
      GiantSignedEdgePromotionBan (giantSignedRawEdgeProduct s r) r.choice.2.1
        (giantSignedPatternFreeLabels C r.bigTarget) := by
  have hr : GiantSignedRawEdgeCondition κ s r := by
    by_contra hn
    exact hne (by simp [giantSignedRawEdgeCoefficient, hn])
  refine ⟨hr, ?_⟩
  by_contra hn
  exact hne (by simp [giantSignedRawEdgeCoefficient, hr, giantSignedEdgeMoveCoefficient, hn])

private theorem particle_rare_of_eq {P : Finset ℕ}
    (x : GiantSignedParticle P) (p : P) (κ : ℤ) (D A B : ℕ) (hD : D = A * B)
    (hx : x = giantSignedParticleAt (-(κ * (D : ℤ))) p) (hban : ¬ p.val ∣ D) :
    x.2 + ((κ : ZMod x.1.val) * (B : ZMod x.1.val)) * (A : ZMod x.1.val) = 0 ∧
      ¬ x.1.val ∣ B * A := by
  subst x
  subst D
  constructor
  · dsimp [giantSignedParticleAt]
    push_cast
    change -((κ : ZMod p.val) * ((A : ZMod p.val) * (B : ZMod p.val))) +
      (κ : ZMod p.val) * (B : ZMod p.val) * (A : ZMod p.val) = 0
    rw [← mul_assoc, mul_right_comm (κ : ZMod p.val) (B : ZMod p.val) (A : ZMod p.val), neg_add_cancel]
  · simpa only [giantSignedParticleAt, mul_comm] using hban

theorem giantSignedRawEdgeCoefficient_promotion_sourceRareGate
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hne : giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r ≠ 0)
    (hprom : r.choice.2.1 ≠ fun _ => ∅) : GiantSignedRawSourceRareGate κ s r := by
  obtain ⟨_, hhits, hban⟩ := giantSignedRawEdgeCoefficient_conditions ν V κ q ρ θ ζ K s r hne
  have hex : ∃ g, r.choice.2.1 g ≠ ∅ := by
    by_contra hn
    push Not at hn
    exact hprom (funext hn)
  obtain ⟨g, hg⟩ := hex
  let i : Fin (r.choice.2.1 g).card :=
    ⟨0, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hg)⟩
  unfold GiantSignedRawSourceRareGate GiantSignedSmallSourceMemoryAllows
  refine ⟨g, r.choice.2.2 g i, ?_⟩
  exact particle_rare_of_eq _
    (giantSignedEdgeSelected (r.choice.2.1 g) (giantSignedPatternFreeLabels C r.bigTarget g) i)
    κ (giantSignedRawEdgeProduct s r)
    (giantSignedSmallPermutationCopiedProduct s.1.val.2 r.sourceSmallPermutation)
    (giantSignedRawSourceBigProduct s r) (giantSignedRawEdgeProduct_source_factor s r)
    ((giantSignedEdgeHits_iff _ _ _ _).mp hhits g i) (hban g i)

theorem giantSignedRawEdgeCoefficient_store_targetRareGate
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hne : giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r ≠ 0)
    (hstore : r.choice.1 ≠ fun _ => ∅) : GiantSignedRawTargetRareGate κ s r := by
  have hr := (giantSignedRawEdgeCoefficient_conditions ν V κ q ρ θ ζ K s r hne).1
  have hex : ∃ g, r.choice.1 g ≠ ∅ := by
    by_contra hn
    push Not at hn
    exact hstore (funext hn)
  obtain ⟨g, hg⟩ := hex
  let i : Fin (r.choice.1 g).card :=
    ⟨0, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hg)⟩
  let j := Fin.natAdd ((giantSignedEdgeRetrievedIndices r.choice g)ᶜ).card i
  unfold GiantSignedRawTargetRareGate GiantSignedSmallSourceMemoryAllows
  refine ⟨g, j, ?_⟩
  apply particle_rare_of_eq _
    (giantSignedEdgeSelected (r.choice.1 g)
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r) g) i)
    (-κ) (giantSignedRawEdgeProduct s r)
    (giantSignedSmallPermutationCopiedProduct (giantSignedRawEdgeTarget κ s r).1.val.2
      r.targetSmallPermutation) (giantSignedRawTargetBigProduct r)
    (giantSignedRawEdgeProduct_target_factor κ s r hr)
  · have he : -((-κ) * (giantSignedRawEdgeProduct s r : ℤ)) =
        κ * (giantSignedRawEdgeProduct s r : ℤ) := by ring
    rw [he]
    exact giantSignedEdgeTarget_store _ _ _ _ g i
  · exact hr.2.2.2.1 g i

end
end ArtinMatthews
