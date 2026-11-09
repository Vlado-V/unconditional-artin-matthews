module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCoefficient
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeIndices


set_option backward.privateInPublic true
@[expose] public section

/-! Actual edge coefficient and prime-transfer factors match the literal
indexed promotion damping used by the raw-delta row count. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyRawEdge_outgoing_tuple_damping_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (jstar : J) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice) choice.target.1 (hZ _ choice.target.2)) ≤
      markedRawPromotionTupleDamping s.2.2 ((markedDirtyEdgePromotedGroups choice.promotions).erase jstar)
        choice.target.1 (hZ _ choice.target.2) ρ (fun _ => 0)
        (markedDirtyEdgeOtherPromotionTuple s.2.2 choice.promotions jstar) := by
  classical
  let I := (markedDirtyEdgePromotedGroups choice.promotions).erase jstar
  let indices := markedDirtyEdgeOtherPromotionTuple s.2.2 choice.promotions jstar
  have hi (j : I) : choice.promotions j.1=some (indices j) :=
    markedDirtyEdgeOtherPromotionTuple_spec s.2.2 choice.promotions jstar j
  have hhit (j : I) : indices j ∈ markedRawGroupHitIndices s.2.2 j.1 choice.target.1 (hZ _ choice.target.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,choice.promotion_hits j.1 (indices j) (hi j)⟩
  have he : markedRawPromotionTupleDamping s.2.2 I choice.target.1 (hZ _ choice.target.2) ρ
      (fun _ => 0) indices = ∏ j : I, ρ^((markedRawPromotionRemainingHits s.2.2 j.1 choice.target.1
        (hZ _ choice.target.2) (indices j)).card) := by
    unfold markedRawPromotionTupleDamping
    exact Finset.prod_congr rfl (fun j _ => by rw [ite_eq_left (hhit j),Nat.add_zero])
  rw [he]
  exact markedDirtyRawEdge_outgoing_damping_le hZ s choice I indices hi hρ₀ hρ₁

theorem markedDirtyRawEdge_delta_promotion_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y : ℝ)
    {ρ H W : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) (jstar : J) :
    ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice‖ ≤
      H^2*W*markedRawPromotionTupleDamping s.2.2 ((markedDirtyEdgePromotedGroups choice.promotions).erase jstar)
        choice.target.1 (hZ _ choice.target.2) ρ (fun _ => 0)
        (markedDirtyEdgeOtherPromotionTuple s.2.2 choice.promotions jstar) :=
  (markedDirtyRawEdge_delta_coefficient_norm_le hZ ψ η d₀ Y hρ₀ hρ₁ hH hW hη hψ χ hχ s choice).trans
    (mul_le_mul_of_nonneg_left (markedDirtyRawEdge_outgoing_tuple_damping_le hZ s choice jstar hρ₀ hρ₁)
      (mul_nonneg (sq_nonneg H) hW))

theorem markedDirtyRawEdge_prime_mass_nonneg {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    0 ≤ markedRawEdgeChoicePrimeMass ν V hZ s choice := by
  apply Finset.prod_nonneg
  intro j _
  split
  · exact hν j _
  · exact (inv_pos.mpr (hV j)).le

theorem markedDirtyRawEdge_prime_mass_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j) {C : ℝ} (hC : 1 ≤ C)
    (hVC : ∀ j, (V j)⁻¹ ≤ C)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice ≤
      finiteProductMass (fun j : markedDirtyEdgeFreshGroups choice.promotions => ν j.1)
        (markedDirtyEdgeFreshTuple s.2.2 choice.promotions choice.fresh)*C^(Fintype.card J) := by
  rw [markedDirtyEdgeChoicePrimeMass_fresh_tuple]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _ => hν _ _))
  calc
    _ ≤ ∏ _j ∈ markedDirtyEdgePromotedGroups choice.promotions, C :=
      Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (hV j)).le) (fun j _ => hVC j)
    _ = C^((markedDirtyEdgePromotedGroups choice.promotions).card) := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Finset.card_le_card (Finset.subset_univ _))

end ArtinMatthews
