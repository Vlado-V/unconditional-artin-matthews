module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute comparison for one countable, one integral, and one finite sector. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem spectralThreeSector_absolute_comparison
    {ι κ : Type*} {β : κ → Type*} [∀ k, Fintype (β k)]
    (S : Finset κ) (f g : ι → ℂ) (u v : ℝ → ℂ) (a b : ∀ k, β k → ℂ) (E : ℝ)
    (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖))
    (hu : IntegrableOn u (Ioi (0 : ℝ))) (hv : IntegrableOn v (Ioi (0 : ℝ)))
    (hfg : ∀ i, ‖f i - g i‖ ≤ E * ‖g i‖)
    (huv : ∀ t, ‖u t - v t‖ ≤ E * ‖v t‖)
    (hab : ∀ k ∈ S, ∀ j, ‖a k j - b k j‖ ≤ E * ‖b k j‖) :
    ‖((∑' i, f i) + ((∫ t in Ioi (0 : ℝ), u t) + ∑ k ∈ S, ∑ j, a k j)) -
      ((∑' i, g i) + ((∫ t in Ioi (0 : ℝ), v t) + ∑ k ∈ S, ∑ j, b k j))‖ ≤
      E * ((∑' i, ‖g i‖) + (∫ t in Ioi (0 : ℝ), ‖v t‖) + ∑ k ∈ S, ∑ j, ‖b k j‖) := by
  have hC : ‖(∑' i, f i) - ∑' i, g i‖ ≤ E * (∑' i, ‖g i‖) := by
    rw [← hf.of_norm.tsum_sub hg.of_norm]
    exact tsum_of_norm_bounded (hg.hasSum.mul_left E) hfg
  have hI : ‖(∫ t in Ioi (0 : ℝ), u t) - ∫ t in Ioi (0 : ℝ), v t‖ ≤
      E * ∫ t in Ioi (0 : ℝ), ‖v t‖ := by
    rw [← integral_sub hu hv, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hv.norm.const_mul E) (ae_of_all _ huv)
  have hR : ‖(∑ k ∈ S, ∑ j, a k j) - ∑ k ∈ S, ∑ j, b k j‖ ≤
      E * ∑ k ∈ S, ∑ j, ‖b k j‖ := by
    rw [show (∑ k ∈ S, ∑ j, a k j) - (∑ k ∈ S, ∑ j, b k j) =
        ∑ k ∈ S, ∑ j, (a k j - b k j) by simp only [Finset.sum_sub_distrib]]
    calc
      _ ≤ ∑ k ∈ S, ‖∑ j, (a k j - b k j)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ S, ∑ j, E * ‖b k j‖ :=
        Finset.sum_le_sum (fun k hk =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hab k hk j)))
      _ = _ := by simp only [Finset.mul_sum]
  calc
    _ = ‖((∑' i, f i) - ∑' i, g i) +
        (((∫ t in Ioi (0 : ℝ), u t) - ∫ t in Ioi (0 : ℝ), v t) +
          ((∑ k ∈ S, ∑ j, a k j) - ∑ k ∈ S, ∑ j, b k j))‖ := by congr 1 <;> ring
    _ ≤ ‖(∑' i, f i) - ∑' i, g i‖ +
        (‖(∫ t in Ioi (0 : ℝ), u t) - ∫ t in Ioi (0 : ℝ), v t‖ +
          ‖(∑ k ∈ S, ∑ j, a k j) - ∑ k ∈ S, ∑ j, b k j‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ E * (∑' i, ‖g i‖) + (E * (∫ t in Ioi (0 : ℝ), ‖v t‖) +
        E * (∑ k ∈ S, ∑ j, ‖b k j‖)) := add_le_add hC (add_le_add hI hR)
    _ = _ := by ring

end
end ArtinMatthews
