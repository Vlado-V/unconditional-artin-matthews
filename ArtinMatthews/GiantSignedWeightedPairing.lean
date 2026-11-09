module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted pairings converge absolutely whenever both actual energies
are finite. Zero weights and arbitrary countable index shapes are allowed. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem giantSignedWeightedPairing_finite {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : ι → ℂ) :
    ‖∑ i ∈ s, (w i : ℂ) * star (f i) * g i‖ ^ 2 ≤
      (∑ i ∈ s, w i * ‖f i‖ ^ 2) * (∑ i ∈ s, w i * ‖g i‖ ^ 2) := by
  have ht : ‖∑ i ∈ s, (w i : ℂ) * star (f i) * g i‖ ≤
      ∑ i ∈ s, w i * ‖f i‖ * ‖g i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖(w i : ℂ) * star (f i) * g i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hw i)]
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

theorem giantSignedWeightedPairing_summable {ι : Type*}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : ι → ℂ)
    (hf : Summable (fun i => w i * ‖f i‖ ^ 2))
    (hg : Summable (fun i => w i * ‖g i‖ ^ 2)) :
    Summable (fun i => (w i : ℂ) * star (f i) * g i) := by
  apply Summable.of_norm_bounded (hf.add hg)
  intro i
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  have h : ‖f i‖ * ‖g i‖ ≤ ‖f i‖ ^ 2 + ‖g i‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f i‖ - ‖g i‖), sq_nonneg ‖f i‖, sq_nonneg ‖g i‖]
  nlinarith [mul_le_mul_of_nonneg_left h (hw i)]

theorem giantSignedWeightedPairing_sq_le {ι : Type*}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : ι → ℂ)
    (hf : Summable (fun i => w i * ‖f i‖ ^ 2))
    (hg : Summable (fun i => w i * ‖g i‖ ^ 2)) :
    ‖∑' i, (w i : ℂ) * star (f i) * g i‖ ^ 2 ≤
      (∑' i, w i * ‖f i‖ ^ 2) * (∑' i, w i * ‖g i‖ ^ 2) := by
  have hp := giantSignedWeightedPairing_summable w hw f g hf hg
  exact le_of_tendsto_of_tendsto (hp.hasSum.norm.pow 2) (Filter.Tendsto.mul hf.hasSum hg.hasSum)
    (Filter.Eventually.of_forall fun s => giantSignedWeightedPairing_finite s w hw f g)

theorem giantSignedWeightedEnergy_summable {ι : Type*}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : ι → ℂ)
    (hf : (∑' i, ENNReal.ofReal (w i * ‖f i‖ ^ 2)) ≠ ∞) :
    Summable (fun i => w i * ‖f i‖ ^ 2) := by
  have h := ENNReal.summable_toReal hf
  apply h.congr
  intro i
  exact ENNReal.toReal_ofReal (mul_nonneg (hw i) (sq_nonneg _))

end
end ArtinMatthews
