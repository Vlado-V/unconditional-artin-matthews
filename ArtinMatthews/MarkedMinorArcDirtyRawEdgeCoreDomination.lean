module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFreshInteger
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedFactors
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeTargetMap
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCoreGate


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise domination of literal nonzero delta edge choices by the actual
counted core; no state or transfer coefficient is replaced by an assumption. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawEdge_delta_choice_core_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {C : ℝ} (hC : 1 ≤ C) (hVC : ∀ j, (V j)⁻¹ ≤ C)
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y : ℝ)
    {ρ H W : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (jstar : J) (hstar : jstar ∈ I)
    (Q : Finset ℤ) (hQ : markedDirtyRawEdgeTrials s.2.1 s.2.2 (I.erase jstar) ⊆ Q)
    (σ : J → Equiv.Perm (Fin (pads+1)))
    (choice : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I) :
    let code := markedDirtyFixedEdgeChoiceCode hZ (markedRawSlotEquiv σ s) I choice
    markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 *
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
        (markedRawSlotEquiv σ s) choice.1‖ ≤
      (C^(Fintype.card J)*H^2*W)*
        finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) code.2.2.2 *
        markedDirtyRawCoreGate s.2.1 s.2.2 jstar (I.erase jstar) Z hZ s.1.1
          (markedDirtyRawFreshIntegerProduct code.2.2.2) Q ρ
          (fun j => σ j (Fin.last pads)) (code.2.2.1 ⟨jstar,hstar⟩) code.1
          (markedDirtyPromotionTupleErase code.2.2.1 jstar) := by
  classical
  let code : Z × ((J → Bool) × (MarkedRawPromotionTuple s.2.2 I ×
      ((j : ↥(Finset.univ \ I)) → ↥(P j.1)))) :=
    markedDirtyFixedEdgeChoiceCode hZ (markedRawSlotEquiv σ s) I choice
  let kstar := code.2.2.1 ⟨jstar,hstar⟩
  let T : ℕ := ∏ j : ↥(Finset.univ \ I), ((code.2.2.2 j).1:ℕ)
  let other := markedDirtyPromotionTupleErase code.2.2.1 jstar
  have hfresh : 0 ≤ finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) code.2.2.2 :=
    Finset.prod_nonneg (fun j _ => hν _ _)
  by_cases hn : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
      (markedRawSlotEquiv σ s) choice.1=0
  · rw [hn,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hfresh)
      (markedDirtyRawCoreGate_nonneg _ _ _ _ _ _ _ _ _ hρ₀ _ _ _ _)
  have hk : choice.1.promotions jstar=some kstar :=
    markedDirtyFixedPromotionTuple_spec s.2.2 choice.1.promotions I choice.2 ⟨jstar,hstar⟩
  have hQ' : markedDirtyRawEdgeTrials s.2.1 s.2.2
      ((markedDirtyEdgePromotedGroups choice.1.promotions).erase jstar) ⊆ Q := by
    simpa only [choice.2] using hQ
  have hmem := markedDirtyRawEdge_delta_target_mem_after_slots hZ ψ η d₀ Y ρ χ s σ choice.1
    jstar kstar hk Q hQ' hn
  have ho := markedDirtyFixedEdgeChoice_other_product hZ (markedRawSlotEquiv σ s) I choice jstar
  have ht := markedDirtyFixedEdgeChoice_fresh_product hZ (markedRawSlotEquiv σ s) I choice
  change markedDirtyEdgeOtherPromotedProduct s.2.2 choice.1.promotions choice.1.fresh jstar=
    markedRawPromotionTuplePrimeProduct s.2.2 (I.erase jstar) other at ho
  change markedDirtyEdgeFreshProduct s.2.2 choice.1.promotions choice.1.fresh=T at ht
  simp only [choice.2] at hmem
  rw [ho,ht] at hmem
  have hs := markedDirtyRawEdge_delta_support hZ ψ η d₀ Y ρ χ (markedRawSlotEquiv σ s) choice.1 hn
  have hban : ¬MarkedRawFullCrossBan s.2.1 (markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh) :=
    (markedDirtyRawStateSlot_crossBan_iff σ s _).not.mp hs.2.2.1
  have hindex : kstar ∈ markedRawDirtyDistinguishedIndices s.2.1 s.2.2 jstar := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro j k
    have hh := markedDirtyEdgeCrossBan_prime_ne s.2.1 _ hban j k jstar
    rwa [markedRawEdgeTargetLast_promoted s.2.2 choice.1.promotions choice.1.fresh jstar kstar hk] at hh
  change _ ≤ (C^(Fintype.card J)*H^2*W)*
    finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) code.2.2.2 *
    markedDirtyRawCoreGate s.2.1 s.2.2 jstar (I.erase jstar) Z hZ s.1.1 T Q ρ
      (fun j => σ j (Fin.last pads)) kstar code.1 other
  unfold markedDirtyRawCoreGate
  rw [ite_eq_left ⟨hindex,hmem⟩]
  have hmass : markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 ≤
      finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) code.2.2.2*C^(Fintype.card J) := by
    rw [markedDirtyFixedEdgeChoice_prime_mass]
    apply mul_le_mul_of_nonneg_left _ hfresh
    calc
      _ ≤ ∏ _j ∈ I, C := Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (hV j)).le) (fun j _ => hVC j)
      _ = C^(I.card) := by simp
      _ ≤ _ := pow_le_pow_right₀ hC (Finset.card_le_card (Finset.subset_univ I))
  have hcoeff := (markedDirtyRawEdge_delta_coefficient_norm_le hZ ψ η d₀ Y hρ₀ hρ₁ hH hW hη hψ χ hχ
    (markedRawSlotEquiv σ s) choice.1).trans (mul_le_mul_of_nonneg_left
      (markedDirtyFixedEdgeChoice_outgoing_damping_le hZ (markedRawSlotEquiv σ s) I choice jstar hρ₀ hρ₁)
      (mul_nonneg (sq_nonneg H) hW))
  change ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
      (markedRawSlotEquiv σ s) choice.1‖ ≤ H^2*W*
    markedRawPromotionTupleDamping s.2.2 (I.erase jstar) code.1.1 (hZ _ code.1.2) ρ (fun _ => 0) other at hcoeff
  have hh := mul_le_mul hmass hcoeff (norm_nonneg _) (mul_nonneg hfresh (pow_nonneg (by linarith) _))
  exact hh.trans_eq (by ring)

end ArtinMatthews
