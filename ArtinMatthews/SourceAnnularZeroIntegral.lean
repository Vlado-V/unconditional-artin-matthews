module

public import ArtinMatthews.SourceAnnularBump
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-bump construction at a complex place: smooth compact
support away from zero, zero additive mass, and a nonzero 5/6 local zeta
pairing. The Fourier-side identity still requires the local functional
equation; it is not presumed in this construction. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff Topology
noncomputable section

theorem sourceAnnularWeightedBump_dilate (z : ℂ) :
    sourceAnnularBump ((2 : ℝ) • z) * ‖z‖ ^ (-(1 / 3 : ℝ)) =
      (2 : ℝ) ^ (1 / 3 : ℝ) * sourceAnnularWeightedBump ((2 : ℝ) • z) := by
  have hc : (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  unfold sourceAnnularWeightedBump
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.mul_rpow (by norm_num) (norm_nonneg z)]
  calc
    _ = ((2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (-(1 / 3 : ℝ))) *
        (sourceAnnularBump ((2 : ℝ) • z) * ‖z‖ ^ (-(1 / 3 : ℝ))) := by rw [hc, one_mul]
    _ = _ := by ring

theorem sourceAnnularWeightedBump_dilate_integrable :
    Integrable (fun z : ℂ => sourceAnnularBump ((2 : ℝ) • z) * ‖z‖ ^ (-(1 / 3 : ℝ))) := by
  have h := (sourceAnnularWeightedBump_integrable.comp_smul
    (by norm_num : (2 : ℝ) ≠ 0)).const_mul ((2 : ℝ) ^ (1 / 3 : ℝ))
  exact h.congr (Filter.Eventually.of_forall fun z => (sourceAnnularWeightedBump_dilate z).symm)

theorem sourceAnnularWeightedBump_dilate_integral :
    (∫ z : ℂ, sourceAnnularBump ((2 : ℝ) • z) * ‖z‖ ^ (-(1 / 3 : ℝ))) =
      ((2 : ℝ) ^ (1 / 3 : ℝ) / 4) * ∫ z : ℂ, sourceAnnularWeightedBump z := by
  simp_rw [sourceAnnularWeightedBump_dilate]
  rw [integral_const_mul, integral_comp_smul volume sourceAnnularWeightedBump 2]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  norm_num
  ring

def sourceAnnularZeroTest (z : ℂ) : ℝ :=
  sourceAnnularBump z - 4 * sourceAnnularBump ((2 : ℝ) • z)

theorem sourceAnnularZeroTest_smooth : ContDiff ℝ ∞ sourceAnnularZeroTest :=
  sourceAnnularBump_smooth.sub
    (contDiff_const.mul (sourceAnnularBump_smooth.comp
      (contDiff_const_smul (2 : ℝ))))

theorem sourceAnnularZeroTest_compact : HasCompactSupport sourceAnnularZeroTest := by
  have hs : HasCompactSupport (fun z : ℂ => sourceAnnularBump ((2 : ℝ) • z)) :=
    sourceAnnularBump_compact.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (2 : ℝ) (by norm_num)))
  exact sourceAnnularBump_compact.sub hs.mul_left

theorem sourceAnnularZeroTest_integrable : Integrable sourceAnnularZeroTest :=
  sourceAnnularZeroTest_smooth.continuous.integrable_of_hasCompactSupport sourceAnnularZeroTest_compact

theorem sourceAnnularZeroTest_integral : (∫ z : ℂ, sourceAnnularZeroTest z) = 0 := by
  unfold sourceAnnularZeroTest
  rw [integral_sub sourceAnnularBump_integrable
    ((sourceAnnularBump_integrable.comp_smul (by norm_num : (2 : ℝ) ≠ 0)).const_mul 4),
    integral_const_mul, integral_comp_smul volume sourceAnnularBump 2]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  norm_num
  ring

theorem sourceAnnularZeroTest_tsupport :
    tsupport sourceAnnularZeroTest ⊆ {z : ℂ | (3 / 8 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 5 / 4} := by
  apply closure_minimal
  · intro z hz
    have hne : sourceAnnularBump z ≠ 0 ∨ sourceAnnularBump ((2 : ℝ) • z) ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      dsimp only [sourceAnnularZeroTest]
      rw [h.1, h.2]
      norm_num
    rcases hne with h | h
    · have hb := sourceAnnularBump_norm_bounds (subset_tsupport _ h)
      constructor <;> linarith [hb.1, hb.2]
    · have hb := sourceAnnularBump_norm_bounds (subset_tsupport _ h)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
      constructor <;> linarith [hb.1, hb.2]
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

theorem sourceAnnularZeroTest_away_zero :
    tsupport sourceAnnularZeroTest ⊆ {z : ℂ | z ≠ 0} := by
  intro z hz hzero
  have hb := (sourceAnnularZeroTest_tsupport hz).1
  norm_num [hzero] at hb

theorem sourceAnnularZeroTest_weighted_integrable :
    Integrable (fun z : ℂ => sourceAnnularZeroTest z * ‖z‖ ^ (-(1 / 3 : ℝ))) := by
  have h := sourceAnnularWeightedBump_integrable.sub
    (sourceAnnularWeightedBump_dilate_integrable.const_mul 4)
  exact h.congr (Filter.Eventually.of_forall fun z => by
    dsimp [sourceAnnularZeroTest, sourceAnnularWeightedBump]
    ring)

theorem sourceAnnularZeroTest_weighted_integral :
    (∫ z : ℂ, sourceAnnularZeroTest z * ‖z‖ ^ (-(1 / 3 : ℝ))) =
      (1 - (2 : ℝ) ^ (1 / 3 : ℝ)) * ∫ z : ℂ, sourceAnnularWeightedBump z := by
  have heq : (fun z : ℂ => sourceAnnularZeroTest z * ‖z‖ ^ (-(1 / 3 : ℝ))) =
      (fun z : ℂ => sourceAnnularWeightedBump z -
        4 * (sourceAnnularBump ((2 : ℝ) • z) * ‖z‖ ^ (-(1 / 3 : ℝ)))) := by
    funext z
    dsimp [sourceAnnularZeroTest, sourceAnnularWeightedBump]
    ring
  rw [heq, integral_sub sourceAnnularWeightedBump_integrable
    (sourceAnnularWeightedBump_dilate_integrable.const_mul 4), integral_const_mul,
    sourceAnnularWeightedBump_dilate_integral]
  ring

theorem sourceAnnularZeroTest_weighted_integral_neg :
    (∫ z : ℂ, sourceAnnularZeroTest z * ‖z‖ ^ (-(1 / 3 : ℝ))) < 0 := by
  rw [sourceAnnularZeroTest_weighted_integral]
  apply mul_neg_of_neg_of_pos
  · have h : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith
  · exact sourceAnnularWeightedBump_integral_pos

/-- The concrete local test required before applying the local zeta functional equation. -/
theorem exists_source_annular_zero_test :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ {z : ℂ | z ≠ 0} ∧ (∫ z : ℂ, f z) = 0 ∧
      Integrable (fun z : ℂ => f z * ‖z‖ ^ (-(1 / 3 : ℝ))) ∧
      (∫ z : ℂ, f z * ‖z‖ ^ (-(1 / 3 : ℝ))) ≠ 0 :=
  ⟨sourceAnnularZeroTest, sourceAnnularZeroTest_smooth, sourceAnnularZeroTest_compact,
    sourceAnnularZeroTest_away_zero, sourceAnnularZeroTest_integral,
    sourceAnnularZeroTest_weighted_integrable, ne_of_lt sourceAnnularZeroTest_weighted_integral_neg⟩

end
end ArtinMatthews.VaryingKummerAnalytic
