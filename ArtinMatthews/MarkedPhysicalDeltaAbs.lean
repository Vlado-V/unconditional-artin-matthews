module

public import ArtinMatthews.MarkedPhysicalDeltaCount
public import ArtinMatthews.MarkedPhysicalScalarDetector


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute delta mass on one fixed coprime pair of last labels. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem markedPhysicalScalarDeltaTerm_norm_le
    (η : ℝ → ℂ) (ψ : ℝ → ℂ) (Y : ℝ) (α β : ℕ → ℂ)
    {A B W : ℝ} (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (b a : ℕ) (v u : ℕ×ℕ) (hvm : ‖α v.1‖ ≤ A) (hum : ‖α u.1‖ ≤ A)
    (hvn : ‖β v.2‖ ≤ B) (hun : ‖β u.2‖ ≤ B) :
    ‖markedPhysicalScalarDetectorTerm η Y (markedRawEdgeDeltaDetector ψ Y) α β b a v u‖ ≤
      if MarkedPhysicalScalarDelta b a v u then (A*B)^2*W else 0 := by
  unfold markedPhysicalScalarDetectorTerm markedPhysicalScalarCofactorTerm markedRawEdgeDeltaDetector
  dsimp only
  by_cases ht : MarkedPhysicalScalarDelta b a v u
  · have hA : 0 ≤ A := (norm_nonneg _).trans hvm
    have hB : 0 ≤ B := (norm_nonneg _).trans hvn
    have hW : 0 ≤ W := (norm_nonneg _).trans (hψ 0)
    rw [ite_eq_left ht]
    unfold MarkedPhysicalScalarDelta at ht
    rw [ite_eq_left ht]
    simp only [mul_one,norm_mul,Complex.norm_conj]
    calc
      _ ≤ 1*1*W*(A*A*B*B) := by
        gcongr
        all_goals
          first
          | exact hη _
          | exact hψ _
      _ = _ := by ring
  · rw [ite_eq_right ht]
    unfold MarkedPhysicalScalarDelta at ht
    rw [ite_eq_right ht]
    simp

theorem markedPhysicalScalarDeltaAbsBlock_le
    (S T : Finset ℕ) {a b Z : ℕ} {Y A B W : ℝ}
    (hY : 0 < Y) (haY : Y ≤ (a:ℝ)) (hbY : Y ≤ (b:ℝ))
    (hcop : a.Coprime b) (haZ : a^4 ≤ Z) (hbZ : b^4 ≤ Z)
    (hR : ∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z)
    (η : ℝ → ℂ) (ψ : ℝ → ℂ) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W) (hW : 0 ≤ W)
    (α β : ℕ → ℂ) (hα : ∀ m∈S,‖α m‖ ≤ A) (hβ : ∀ n∈T,‖β n‖ ≤ B) :
    markedPhysicalScalarDetectorAbsBlock S T η Y (markedRawEdgeDeltaDetector ψ Y) α β b a ≤
      ((A*B)^2*W)*(8*(Z:ℝ)/Y*(1+Real.log (Z:ℝ))^3) := by
  unfold markedPhysicalScalarDetectorAbsBlock
  calc
    _ ≤ ∑ v ∈ S.product T,∑ u ∈ S.product T,
        if MarkedPhysicalScalarDelta b a v u then (A*B)^2*W else 0 := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨hvm,hvn⟩ := Finset.mem_product.mp hv
      obtain ⟨hum,hun⟩ := Finset.mem_product.mp hu
      exact markedPhysicalScalarDeltaTerm_norm_le η ψ Y α β hη hψ b a v u
        (hα _ hvm) (hα _ hum) (hβ _ hvn) (hβ _ hun)
    _ = ((A*B)^2*W)*(∑ v ∈ S.product T,∑ u ∈ S.product T,
        if MarkedPhysicalScalarDelta b a v u then (1:ℝ) else 0) := by
      simp only [Finset.mul_sum,mul_ite,mul_zero,mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (markedPhysicalScalarDelta_count_le S T hY haY hbY hcop haZ hbZ hR) (mul_nonneg (sq_nonneg _) hW)

end
end ArtinMatthews
