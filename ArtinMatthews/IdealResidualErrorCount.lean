module

public import ArtinMatthews.IdealResidualCost


set_option backward.privateInPublic true
@[expose] public section

/-! Direct averaging retains every nonempty comparison pair. Its
error count depends only on the designated probes. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualErrors_norm {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J) (E : Finset I → Finset J → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ∀ A∈S.powerset.erase ∅,∀ B∈T.powerset.erase ∅,‖E A B‖ ≤ ε) :
    ‖∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,E A B‖ ≤
      (2:ℝ)^(S.card+T.card)*ε := by
  have hA : (S.powerset.erase ∅).card ≤ 2^S.card :=
    (card_le_card (erase_subset _ _)).trans_eq (card_powerset S)
  have hB : (T.powerset.erase ∅).card ≤ 2^T.card :=
    (card_le_card (erase_subset _ _)).trans_eq (card_powerset T)
  have hAr : ((S.powerset.erase ∅).card:ℝ) ≤ (2:ℝ)^S.card := by exact_mod_cast hA
  have hBr : ((T.powerset.erase ∅).card:ℝ) ≤ (2:ℝ)^T.card := by exact_mod_cast hB
  calc
    _ ≤ ∑ A∈S.powerset.erase ∅,‖∑ B∈T.powerset.erase ∅,E A B‖ := norm_sum_le _ _
    _ ≤ ∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,‖E A B‖ :=
      sum_le_sum fun A _ => norm_sum_le _ _
    _ ≤ ∑ _A∈S.powerset.erase ∅,∑ _B∈T.powerset.erase ∅,ε :=
      sum_le_sum fun A hA => sum_le_sum fun B hB => hE A hA B hB
    _ = ((S.powerset.erase ∅).card:ℝ)*((T.powerset.erase ∅).card:ℝ)*ε := by
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((2:ℝ)^S.card*(2:ℝ)^T.card)*ε :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hAr hBr (Nat.cast_nonneg _) (by positivity)) hε
    _ = _ := by rw [pow_add]

end
end ArtinMatthews
