module

public import ArtinMatthews.MarkedMinorArcDirtyGoodRow
public import ArtinMatthews.MarkedMinorArcDirtyCrudeTargets


set_option backward.privateInPublic true
@[expose] public section

/-! The exceptional fresh draw costs the actual finite pending-index count;
the source omissions are still averaged, never counted without normalization. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedRawPromotionTuple_card_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) :
    Fintype.card (MarkedRawPromotionTuple memory I) ≤ B^(I.card) := by
  classical
  calc
    _ = ∏ j : I, (memory.1.1 j.1:ℕ) := by simp [MarkedRawPromotionTuple,Fintype.card_pi]
    _ ≤ ∏ _j : I, B := Finset.prod_le_prod (fun j _ => markedRawMemory_group_size_le memory j.1)
    _ = _ := by simp

theorem markedRawPromotionProductSupport_card_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) :
    (markedRawPromotionProductSupport memory I).card ≤ B^(I.card) := by
  apply Finset.card_image_le.trans
  simpa only [Finset.card_univ] using markedRawPromotionTuple_card_le memory I

theorem markedRawDirtyGoodChoiceMass_crude_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (hM : 0 < M) (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (newHits : (J → Fin M) → V → I → ℕ) :
    markedRawDirtyGoodChoiceMass source memory jstar I V hV z T Q ρ newHits ≤
      33*(B:ℝ)^(I.card+1)*(1/(1-ρ)^2)^(I.card) := by
  classical
  let C : ℝ := (1/(1-ρ)^2)^(I.card)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let H := markedRawDirtyDistinguishedIndices source memory jstar
  have hH : H.card ≤ B := by
    calc
      _ ≤ (Finset.univ : Finset (Fin (memory.1.1 jstar:ℕ))).card := Finset.card_filter_le _ _
      _ = (memory.1.1 jstar:ℕ) := by simp
      _ ≤ B := markedRawMemory_group_size_le memory jstar
  have hweight (o : J → Fin M) : 0 ≤ markedUniformOmissionWeight M o := by
    rw [markedUniformOmissionWeight_eq]
    positivity
  have hpoint (k) :
      (∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
        (markedRawPromotionProductSupport memory I) V hV z T Q,
        markedUniformOmissionWeight M c.1.1 *
          ∑ t ∈ Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
            markedRawPromotionTuplePrimeProduct memory I t=c.1.2),
            markedRawPromotionTupleDamping memory I c.2.1 (hV _ c.2.2) ρ (newHits c.1.1 c.2) t) ≤
        (33*(B:ℝ)^(I.card))*C := by
    calc
      _ ≤ ∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
          (markedRawPromotionProductSupport memory I) V hV z T Q,
          markedUniformOmissionWeight M c.1.1*C := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left (markedRawPromotionTupleDamping_product_fiber_le
          memory I c.2.1 (hV _ c.2.2) hρ₀ hρ₁ (newHits c.1.1 c.2) c.1.2) (hweight _)
      _ = (∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
          (markedRawPromotionProductSupport memory I) V hV z T Q,
          markedUniformOmissionWeight M c.1.1)*C := (Finset.sum_mul _ _ _).symm
      _ ≤ (33*((markedRawPromotionProductSupport memory I).card:ℝ))*C :=
        mul_le_mul_of_nonneg_right (markedRawDirtyTargetChoices_crude_weight_le hM source
          (memory.2 jstar k) (markedRawPromotionProductSupport memory I) V hV z w T Q r hd hz hbox) hC
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by exact_mod_cast markedRawPromotionProductSupport_card_le memory I) (by norm_num)) hC
  calc
    _ ≤ ∑ _k ∈ H, (33*(B:ℝ)^(I.card))*C := Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (H.card:ℝ)*((33*(B:ℝ)^(I.card))*C) := by simp
    _ ≤ (B:ℝ)*((33*(B:ℝ)^(I.card))*C) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by positivity)
    _ = _ := by dsimp [C]; rw [pow_succ]; ring

end ArtinMatthews
