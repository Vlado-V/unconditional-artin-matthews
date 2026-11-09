module

public import ArtinMatthews.SpectralPoincareUnfoldingMultiplicity
public import ArtinMatthews.SpectralPoincareUnfoldingSupport
public import ArtinMatthews.SpectralGamma0CompactMass


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compactly supported modular unfolding for invariant hyperbolic
measure.  The full integral identity has multiplicity two from the actual
central kernel; all sum-integral exchanges are finite on compact supports. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups CompactlySupported Pointwise

namespace ArtinMatthews

theorem modular_integral_finsum_eq_two_integral (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∑ᶠ g : SL(2, ℤ), ∫ z in ModularGroup.fd, F (g⁻¹ • z)) = 2 * ∫ z, F z := by
  classical
  let K := tsupport F
  let hf := compact_modular_translates_meeting_fd_finite hFc
  let s := hf.toFinset
  let D (g : SL(2, ℤ)) := (fun z : UpperHalfPlane => g • z) ⁻¹' ModularGroup.fdo
  have hD (g : SL(2, ℤ)) : MeasurableSet (D g) :=
    ModularGroup.isOpen_fdo.measurableSet.preimage (h2_integer_measurePreserving g).measurable
  have hint : Integrable F := hF.integrable_of_hasCompactSupport hFc
  have hzero (g : SL(2, ℤ)) (hg : g ∉ s) (z : UpperHalfPlane)
      (hz : z ∈ ModularGroup.fd) : F (g⁻¹ • z) = 0 := by
    by_contra hn
    apply hg
    exact hf.mem_toFinset.mpr ⟨z,
      ⟨g⁻¹ • z, subset_tsupport F hn, smul_inv_smul g z⟩, hz⟩
  have hsupport : Function.support (fun g : SL(2, ℤ) =>
      ∫ z in ModularGroup.fd, F (g⁻¹ • z)) ⊆ s := by
    intro g hg
    by_contra hgs
    apply hg
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    exact hzero g hgs z hz
  have hchange (g : SL(2, ℤ)) :
      (∫ z, (D g).indicator F z) = ∫ z in ModularGroup.fd, F (g⁻¹ • z) := by
    rw [integral_indicator (hD g), modular_restrict_fd_eq_fdo]
    have hme : MeasurableEmbedding (fun z : UpperHalfPlane => g • z) := by
      change MeasurableEmbedding
        (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z)
      exact measurableEmbedding_const_smul _
    simpa only [inv_smul_smul, D] using (h2_integer_measurePreserving g).setIntegral_preimage_emb
      hme (fun z : UpperHalfPlane => F (g⁻¹ • z)) ModularGroup.fdo
  have hpoint (z : UpperHalfPlane) :
      (∑ᶠ g : SL(2, ℤ), (D g).indicator F z) = ∑ g ∈ s, (D g).indicator F z := by
    apply finsum_eq_sum_of_support_subset
    intro g hg
    change (D g).indicator F z ≠ 0 at hg
    have hdz : g • z ∈ ModularGroup.fdo := by
      by_contra h
      exact hg (indicator_of_notMem (show z ∉ D g from h) F)
    have hFz : F z ≠ 0 := by
      simpa only [indicator_of_mem (show z ∈ D g from hdz)] using hg
    exact hf.mem_toFinset.mpr ⟨g • z,
      ⟨z, subset_tsupport F hFz, rfl⟩, ModularGroup.fdo_subset_fd hdz⟩
  calc
    _ = ∑ g ∈ s, ∫ z in ModularGroup.fd, F (g⁻¹ • z) :=
      finsum_eq_sum_of_support_subset _ hsupport
    _ = ∑ g ∈ s, ∫ z, (D g).indicator F z :=
      Finset.sum_congr rfl fun g _ => (hchange g).symm
    _ = ∫ z, ∑ g ∈ s, (D g).indicator F z :=
      (integral_finsetSum s fun g _ => hint.indicator (hD g)).symm
    _ = ∫ z, 2 * F z := by
      apply integral_congr_ae
      filter_upwards [modular_fdo_indicator_finsum_ae F] with z hz
      exact (hpoint z).symm.trans hz
    _ = 2 * ∫ z, F z := integral_const_mul 2 F

end ArtinMatthews
