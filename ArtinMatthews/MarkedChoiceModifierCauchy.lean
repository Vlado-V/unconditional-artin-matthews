module

public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded multiplier on each literal choice preserves the absolute
Cauchy majorant. This statement gives a crude estimate only; it makes no
claim that a signed cancellation estimate survives an arbitrary modifier. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedChoiceModifier_finite_cauchy {ι : Type*} [Fintype ι]
    (c f modifier : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, ‖modifier i‖ ≤ 1) :
    ‖∑ i, c i*(modifier i*f i)‖^2 ≤
      (∑ i, ‖c i‖*w i)*(∑ i, ‖c i‖/w i*‖f i‖^2) := by
  apply (markedGhostChoice_finite_cauchy c (fun i => modifier i*f i) w hw).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hw i).le))
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (norm_nonneg _) (hw i).le)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)).trans_eq (one_mul _)

end ArtinMatthews
