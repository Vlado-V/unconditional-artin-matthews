module

public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


set_option backward.privateInPublic true
@[expose] public section

/-!
The boundary of the standard modular domain is null for the actual invariant
hyperbolic measure.  The proof transfers the two vertical lines and the unit
circle from complex Lebesgue measure; it does not posit a fundamental-domain
measure identity or a free action of `SL(2, ℤ)`.
-/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- Complex Lebesgue null sets remain null after restriction to the upper
half-plane and multiplication by the actual hyperbolic density. -/
theorem h2_volume_preimage_null {s : Set ℂ} (hs : volume s = 0) :
    volume (UpperHalfPlane.coe ⁻¹' s) = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  exact measure_mono_null (image_preimage_subset _ _) hs

/-- A vertical line is null for complex Lebesgue measure. -/
theorem complex_vertical_line_volume_zero (c : ℝ) :
    volume {z : ℂ | z.re = c} = 0 := by
  have hprod : (volume : Measure (ℝ × ℝ)) ({c} ×ˢ univ) = 0 := by
    simp [Measure.volume_eq_prod, Measure.prod_prod]
  have hp := (Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet).trans hprod
  convert hp using 2
  ext z
  simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff, mem_univ,
    and_true, Complex.measurableEquivRealProd_apply]

/-- The unit circle is null for complex Lebesgue measure. -/
theorem complex_unit_circle_volume_zero :
    volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere 0 1 := by
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right]
    have hn := norm_nonneg z
    change Complex.normSq z = 1 at hz
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith
  exact measure_mono_null hsub (Measure.addHaar_sphere volume (0 : ℂ) 1)

/-- The boundary of the standard modular fundamental domain has zero
hyperbolic measure. -/
theorem modular_fd_sdiff_fdo_volume_zero :
    volume (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  have hcircle : volume {z : UpperHalfPlane | Complex.normSq (z : ℂ) = 1} = 0 :=
    h2_volume_preimage_null complex_unit_circle_volume_zero
  have hright : volume {z : UpperHalfPlane | z.re = 1 / 2} = 0 :=
    h2_volume_preimage_null (complex_vertical_line_volume_zero (1 / 2))
  have hleft : volume {z : UpperHalfPlane | z.re = -(1 / 2)} = 0 :=
    h2_volume_preimage_null (complex_vertical_line_volume_zero (-(1 / 2)))
  apply measure_mono_null (t := {z : UpperHalfPlane | Complex.normSq (z : ℂ) = 1} ∪
    {z : UpperHalfPlane | z.re = 1 / 2} ∪ {z : UpperHalfPlane | z.re = -(1 / 2)})
  · intro z hz
    rcases hz with ⟨⟨hn, hr⟩, hnot⟩
    by_cases heq : Complex.normSq (z : ℂ) = 1
    · exact Or.inl (Or.inl heq)
    · have hnorm : 1 < Complex.normSq (z : ℂ) := lt_of_le_of_ne hn (Ne.symm heq)
      have hre : |z.re| = 1 / 2 := le_antisymm hr (not_lt.mp fun h => hnot ⟨hnorm, h⟩)
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hre with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · exact measure_union_null (measure_union_null hcircle hright) hleft

/-- The open and closed modular regions give the same almost-everywhere set. -/
theorem modular_fd_ae_eq_fdo :
    ModularGroup.fd =ᵐ[volume] ModularGroup.fdo := by
  rw [ae_eq_set]
  exact ⟨modular_fd_sdiff_fdo_volume_zero,
    by simp [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd]⟩

/-- In particular, the two regions define exactly the same restricted measure. -/
theorem modular_restrict_fd_eq_fdo :
    (volume : Measure UpperHalfPlane).restrict ModularGroup.fd =
      volume.restrict ModularGroup.fdo :=
  Measure.restrict_congr_set modular_fd_ae_eq_fdo

end ArtinMatthews
