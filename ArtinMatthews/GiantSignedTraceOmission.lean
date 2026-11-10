module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Doubling pays for every omitted trace, also after imposing a global
path multiplier of modulus at most one. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedTraceOmission_norm_le {T : Type*} (w φ : T → ℂ) (good : T → Prop)
    (births : T → ℕ) (H stores : ℕ) (hφ : ∀ t, ‖φ t‖ ≤ 1)
    (hw : Summable (fun t => ‖w t‖))
    (hdouble : Summable (fun t => (2:ℝ)^births t * ‖w t‖))
    (hfail : ∀ t, ¬ good t → H < births t+stores) :
    ‖(∑' t, w t * φ t) - (∑' t, if good t then w t * φ t else 0)‖ ≤
      (∑' t, (2:ℝ)^births t * ‖w t‖) / (2:ℝ)^(H-stores) := by
  let F := fun t => w t * φ t
  let kept := fun t => if good t then F t else 0
  let out := fun t => if good t then 0 else F t
  have hF (t : T) : ‖F t‖ ≤ ‖w t‖ := by
    rw [show ‖F t‖ = ‖w t‖ * ‖φ t‖ from norm_mul _ _]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφ t)
  have hsF : Summable (fun t => ‖F t‖) := hw.of_nonneg_of_le (fun _ => norm_nonneg _) hF
  have hsK : Summable (fun t => ‖kept t‖) := hsF.of_nonneg_of_le (fun _ => norm_nonneg _) fun t => by
    by_cases ht : good t <;> simp [kept, ht]
  have hsO : Summable (fun t => ‖out t‖) := hsF.of_nonneg_of_le (fun _ => norm_nonneg _) fun t => by
    by_cases ht : good t <;> simp [out, ht]
  have he : (∑' t, F t) - (∑' t, kept t) = ∑' t, out t := by
    rw [← hsF.of_norm.tsum_sub hsK.of_norm]
    exact tsum_congr (fun t => by by_cases ht : good t <;> simp [kept, out, ht])
  let D := (2:ℝ)^(H-stores)
  have hD : 0 < D := pow_pos (by norm_num) _
  change ‖(∑' t, F t) - (∑' t, kept t)‖ ≤ (∑' t, (2:ℝ)^births t * ‖w t‖) / D
  rw [he]
  calc
    _ ≤ ∑' t, ‖out t‖ := norm_tsum_le_tsum_norm hsO
    _ ≤ ∑' t, (2:ℝ)^births t * ‖w t‖ / D := by
      apply hsO.tsum_le_tsum _ (hdouble.div_const D)
      intro t
      by_cases ht : good t
      · simp only [out, ite_eq_left ht, norm_zero]
        exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)) hD.le
      · simp only [out, ite_eq_right ht]
        have hb : H-stores ≤ births t := by have hh := hfail t ht; omega
        apply (le_div_iff₀ hD).2
        calc
          ‖F t‖ * D ≤ ‖w t‖ * D := mul_le_mul_of_nonneg_right (hF t) hD.le
          _ ≤ ‖w t‖ * (2:ℝ)^births t := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by norm_num) hb) (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := tsum_div_const

end
end ArtinMatthews
