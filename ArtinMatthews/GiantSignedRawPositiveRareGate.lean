module

public import ArtinMatthews.GiantSignedRawGateAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Nonzero positive promotion terms force the actual source omission gate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}

theorem giantSignedRawPositiveCoefficient_promotion_sourceRareGate
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ : ℝ)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hne : giantSignedRawPositiveCoefficient ν V κ q ρ s r ≠ 0)
    (hprom : r.choice.2.1 ≠ fun _ => ∅) : GiantSignedRawSourceRareGate κ s r := by
  let D := giantSignedRawEdgeProduct s r
  let a := giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r)
  let b := giantSignedPatternFreeLabels C r.bigTarget
  have hc : giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
      (κ * (D : ℤ)) D a b s.2.2 r.choice ≠ 0 := by
    intro h
    apply hne
    unfold giantSignedRawPositiveCoefficient
    split_ifs
    · change _ * (_ * ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
          (κ * (D : ℤ)) D a b s.2.2 r.choice‖) = 0
      simp only [h, norm_zero, mul_zero]
    · exact mul_zero _
  have hgate : GiantSignedEdgeHits (κ * (D : ℤ)) s.2.2 b r.choice ∧
      GiantSignedEdgePromotionBan D r.choice.2.1 b := by
    by_contra h
    exact hc (by simp only [giantSignedEdgeMoveCoefficient, h, ite_false, mul_zero])
  obtain ⟨hhits,hban⟩ := hgate
  have hex : ∃ g, r.choice.2.1 g ≠ ∅ := by
    by_contra hn
    push Not at hn
    exact hprom (funext hn)
  obtain ⟨g,hg⟩ := hex
  let i : Fin (r.choice.2.1 g).card :=
    ⟨0, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hg)⟩
  let p := giantSignedEdgeSelected (r.choice.2.1 g) (b g) i
  let A := giantSignedSmallPermutationCopiedProduct s.1.val.2 r.sourceSmallPermutation
  let B₀ := giantSignedRawSourceBigProduct s r
  have hD : D = A * B₀ := giantSignedRawEdgeProduct_source_factor s r
  have hp := (giantSignedEdgeHits_iff _ _ _ _).mp hhits g i
  have hp' : (s.2.2.2 g (r.choice.2.2 g i)) =
      giantSignedParticleAt (-(κ * (D : ℤ))) p := hp
  unfold GiantSignedRawSourceRareGate GiantSignedSmallSourceMemoryAllows
  refine ⟨g, r.choice.2.2 g i, ?_⟩
  change (s.2.2.2 g (r.choice.2.2 g i)).2 +
      ((κ : ZMod (s.2.2.2 g (r.choice.2.2 g i)).1.val) * (B₀ : ZMod _)) *
        (A : ZMod _) = 0 ∧
    ¬ (s.2.2.2 g (r.choice.2.2 g i)).1.val ∣ B₀ * A
  rw [hp']
  constructor
  · dsimp only [giantSignedParticleAt]
    rw [hD]
    push_cast
    change -((κ : ZMod p.val) * ((A : ZMod p.val) * (B₀ : ZMod p.val))) +
      (κ : ZMod p.val) * (B₀ : ZMod p.val) * (A : ZMod p.val) = 0
    rw [← mul_assoc, mul_right_comm (κ : ZMod p.val) (B₀ : ZMod p.val) (A : ZMod p.val),
      neg_add_cancel]
  · have hpban : ¬ p.val ∣ D := hban g i
    simpa only [giantSignedParticleAt, hD, mul_comm A B₀] using hpban

end
end ArtinMatthews
