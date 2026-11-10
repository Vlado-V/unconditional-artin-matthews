module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.Modular


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact-chart bounds for modular translates. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

/-- A modular image can rise no higher than y or 1/y. -/
theorem modular_im_smul_le_max (δ : SL(2, ℤ)) (z : UpperHalfPlane) :
    (δ • z).im ≤ max z.im (1 / z.im) := by
  by_cases hc : δ 1 0 = 0
  · obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
    rw [hn, ModularGroup.im_T_zpow_smul]
    exact le_max_left _ _
  · have hc' : (1 : ℝ) ≤ |(δ 1 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hc
    have hc2 : (1 : ℝ) ≤ (δ 1 0 : ℝ) ^ 2 := by nlinarith [sq_abs (δ 1 0 : ℝ)]
    have hden : z.im ^ 2 ≤ Complex.normSq (UpperHalfPlane.denom
        (Matrix.SpecialLinearGroup.mapGL ℝ δ) z) := by
      have h := UpperHalfPlane.c_mul_im_sq_le_normSq_denom
        (Matrix.SpecialLinearGroup.mapGL ℝ δ) z
      have hh : z.im ^ 2 ≤ ((δ 1 0 : ℝ) * z.im) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im)]
      exact hh.trans h
    have him : (δ • z).im ≤ 1 / z.im := by
      rw [ModularGroup.im_smul_eq_div_normSq]
      calc
        _ ≤ z.im / z.im ^ 2 := div_le_div_of_nonneg_left z.im_pos.le (sq_pos_of_pos z.im_pos) hden
        _ = 1 / z.im := by field_simp
    exact him.trans (le_max_right _ _)

/-- Compactness supplies a uniform height bound for all modular images. -/
theorem compact_modular_images_height_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ Y > 0, ∀ δ : SL(2, ℤ), ∀ z ∈ K, (δ • z).im ≤ Y := by
  have hc : Continuous (fun z : UpperHalfPlane => max z.im (1 / z.im)) :=
    UpperHalfPlane.continuous_im.max
      (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_pos.ne'))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, by positivity, fun δ z hz => ?_⟩
  calc
    (δ • z).im ≤ max z.im (1 / z.im) := modular_im_smul_le_max δ z
    _ ≤ ‖max z.im (1 / z.im)‖ := le_abs_self _
    _ ≤ C := hC z hz
    _ ≤ max C 1 := le_max_left _ _

end ArtinMatthews
