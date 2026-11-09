module

public import ArtinMatthews.MarkedPhysicalScalarAbsDyad
public import ArtinMatthews.MarkedPhysicalDeltaAbs
public import ArtinMatthews.MarkedTypeIIScalarMajorJoin
public import ArtinMatthews.MarkedTypeIIAbsoluteMajorBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Actual absolute mass of both coprime scalar detector branches.
Delta uses the progression divisor moment. Major uses its independent
determinant-band count and the true major kernel bound. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedPhysicalCoprimeDelta_abs_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (S T : Finset ℕ) (Z : ℕ) (hZ : 1 ≤ Z)
    (hR : ∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z)
    (η : ℝ → ℂ) (ψ : ℝ → ℂ) {Y A B W : ℝ}
    (hY : 0 < Y) (hW : 0 ≤ W) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hηs : Function.support η ⊆ Set.Icc 1 4)
    (hlabel : ∀ a ∈ markedTypeIIDyadLabels P Y,a^4 ≤ Z)
    (α β : ℕ → ℂ) (hα : ∀ m∈S,‖α m‖ ≤ A) (hβ : ∀ n∈T,‖β n‖ ≤ B) :
    markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y (markedRawEdgeDeltaDetector ψ Y) α β ≤
      128*(markedMajorLabelMass P)^2*(A*B)^2*W*Y*(Z:ℝ)*(1+Real.log (Z:ℝ))^3 := by
  let L := markedPhysicalCoprimeDyadPairs P Y
  let C := ((A*B)^2*W)*(8*(Z:ℝ)/Y*(1+Real.log (Z:ℝ))^3)
  have hlog : 0 ≤ Real.log (Z:ℝ) := Real.log_nonneg (by exact_mod_cast hZ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hc : (L.card:ℝ) ≤ (4*Y)^2 := by
    have hsub : L ⊆ (markedTypeIIDyadLabels P Y).product (markedTypeIIDyadLabels P Y) :=
      Finset.filter_subset _ _
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    rw [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,← pow_two]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (markedTypeIIDyadLabels_card_le P Y hY) 2
  rw [markedPhysicalCoprimeScalarDetectorAbsMass_dyad P S T η hY hηs]
  calc
    _ ≤ (markedMajorLabelMass P)^2*(∑ _z ∈ L,C) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hbox,hcop⟩ := Finset.mem_filter.mp hz
      obtain ⟨hb,ha⟩ := Finset.mem_product.mp hbox
      exact markedPhysicalScalarDeltaAbsBlock_le S T hY (Finset.mem_filter.mp ha).2.1
        (Finset.mem_filter.mp hb).2.1 hcop.symm (hlabel _ ha) (hlabel _ hb) hR η ψ hη hψ hW α β hα hβ
    _ ≤ (markedMajorLabelMass P)^2*((4*Y)^2*C) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hC) (sq_nonneg _)
    _ = _ := by dsimp only [C]; field_simp [hY.ne']; ring

theorem markedPhysicalCoprimeMajor_abs_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (S T : Finset ℕ) (Z : ℕ)
    (hRZ : ∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R A B W : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hηs : Function.support η ⊆ Set.Icc 1 4) (hψs : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (hα : ∀ m∈S,‖α m‖ ≤ A) (hβ : ∀ n∈T,‖β n‖ ≤ B) :
    markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y (markedRawEdgeMajorDetector ψ Q Y) α β ≤
      64*(markedMajorLabelMass P)^2*(A*B)^2*W*(2*R+1)*Q^3*Y*(Z:ℝ)*
        (∑ d ∈ Finset.Icc 1 Z,1/(d:ℝ))^3 := by
  rw [markedPhysicalCoprimeScalarDetectorAbsMass_dyad P S T η hY hηs]
  have hL : markedPhysicalCoprimeDyadPairs P Y ⊆
      (markedTypeIIDyadLabels P Y).product (markedTypeIIDyadLabels P Y) := Finset.filter_subset _ _
  simpa only [one_mul,markedPhysicalScalarDetectorAbsBlock,markedPhysicalScalarDetectorTerm_major,
    Finset.product_eq_sprod] using
    (markedTypeIIScalarMajor_total_abs_le P (markedPhysicalCoprimeDyadPairs P Y) S S T Z
      hRZ hRZ η ψ hQ hY hR hW hA hB hη hψ hψs α β hα hα hβ hL
      (fun _ _ _ => 1) (fun _ _ _ _ _ _ => by simp))

end
end ArtinMatthews
