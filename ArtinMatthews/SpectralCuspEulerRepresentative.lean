module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralCuspEulerUniqueness
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted energy bounds pass from actual measurable constant terms to
their classical representatives.  Regularity itself remains an explicit,
separately proved input. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
noncomputable section

theorem cuspEuler_energy_ae_on_subset {c C : ℝ → ℂ}
    (hrep : C =ᵐ[volume.restrict (Ioi (0 : ℝ))] c)
    {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    (fun y : ℝ => ‖C y‖ ^ 2 / y ^ 2) =ᵐ[volume.restrict s]
      fun y : ℝ => ‖c y‖ ^ 2 / y ^ 2 := by
  filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hs))] with y hy
  rw [hy]

theorem cuspEuler_vanishes_of_ae_energy_bounds (c C C' : ℝ → ℂ)
    (hrep : C =ᵐ[volume.restrict (Ioi (0 : ℝ))] c)
    (hC : ∀ y > 0, HasDerivAt C (C' y) y)
    (hC' : ∀ y > 0, HasDerivAt C' (C y / (y : ℂ) ^ 2) y)
    (htail : IntegrableOn (fun y : ℝ => ‖c y‖ ^ 2 / y ^ 2) (Ioi 1))
    {k B : ℝ} (hk : 0 ≤ k) (hk5 : k < Real.sqrt 5)
    (hnear : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖c y‖ ^ 2 / y ^ 2) ≤ B * Y ^ (-k)) :
    (∀ y > 0, C y = 0) ∧ c =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have htailC : IntegrableOn (fun y : ℝ => ‖C y‖ ^ 2 / y ^ 2) (Ioi 1) :=
    htail.congr (cuspEuler_energy_ae_on_subset hrep (Ioi_subset_Ioi (by norm_num))).symm
  have hnearC : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖C y‖ ^ 2 / y ^ 2) ≤ B * Y ^ (-k) := by
    intro Y hY hY1
    have hs : Icc Y 1 ⊆ Ioi (0 : ℝ) := fun _ hy => hY.trans_le hy.1
    rw [integral_congr_ae (cuspEuler_energy_ae_on_subset hrep hs)]
    exact hnear Y hY hY1
  have hv := cuspEuler_vanishes_of_energy_bounds C C' hC hC' htailC hk hk5 hnearC
  refine ⟨hv, ?_⟩
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioi] with y hy hypos
  exact hy.symm.trans (hv y hypos)

theorem cuspEuler_vanishes_of_ae_quadratic_bound (c C C' : ℝ → ℂ)
    (hrep : C =ᵐ[volume.restrict (Ioi (0 : ℝ))] c)
    (hC : ∀ y > 0, HasDerivAt C (C' y) y)
    (hC' : ∀ y > 0, HasDerivAt C' (C y / (y : ℂ) ^ 2) y)
    (htail : IntegrableOn (fun y : ℝ => ‖c y‖ ^ 2 / y ^ 2) (Ioi 1))
    {B : ℝ} (hnear : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖c y‖ ^ 2 / y ^ 2) ≤ B / Y ^ 2) :
    (∀ y > 0, C y = 0) ∧ c =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  apply cuspEuler_vanishes_of_ae_energy_bounds c C C' hrep hC hC' htail
    (k := 2) (by norm_num) (by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      have hn := Real.sqrt_nonneg (5 : ℝ)
      nlinarith)
  intro Y hY hY1
  simpa only [Real.rpow_neg hY.le, Real.rpow_two, div_eq_mul_inv] using hnear Y hY hY1

end
end ArtinMatthews
