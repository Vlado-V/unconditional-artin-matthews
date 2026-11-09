module

public import ArtinMatthews.SpectralKLUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! Literal physical compact tests and the complex weighted-measure
identities needed for the inverse KL integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKLPositiveWeightMeasure_complex_integral (w : ℝ → ℝ) (F : ℝ → ℂ)
    (hw : Measurable w) (hp : ∀ t : ℝ, 0 < t → 0 ≤ w t) :
    (∫ t, F t ∂spectralKLPositiveWeightMeasure w) =
      ∫ t in Ioi (0 : ℝ), (w t : ℂ)*F t := by
  unfold spectralKLPositiveWeightMeasure
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  have hfin : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal (w t) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul hwd hfin F]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hp t ht),Complex.real_smul]

theorem spectralKLPositiveWeightMeasure_complex_integrable_iff (w : ℝ → ℝ) (F : ℝ → ℂ)
    (hw : Measurable w) (hp : ∀ t : ℝ, 0 < t → 0 ≤ w t) :
    Integrable F (spectralKLPositiveWeightMeasure w) ↔
      IntegrableOn (fun t => (w t : ℂ)*F t) (Ioi (0 : ℝ)) := by
  unfold spectralKLPositiveWeightMeasure
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  have hfin : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal (w t) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' (μ := volume.restrict (Ioi (0 : ℝ)))
    (g := F) hwd hfin).trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hp t ht),Complex.real_smul]

def spectralKLPhysicalCompactDiv (f : ℝ → ℂ) (x : ℝ) : ℂ := f x/(x : ℂ)

theorem spectralKLPhysicalCompactDiv_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) : Continuous (spectralKLPhysicalCompactDiv f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x
  · exact hf.continuousAt.div Complex.continuous_ofReal.continuousAt (by exact_mod_cast hx.ne')
  · have hxs : x ∉ tsupport f := fun h => hx (hfp h)
    have hz : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
    have heq : spectralKLPhysicalCompactDiv f =ᶠ[𝓝 x] 0 := by
      filter_upwards [hz] with y hy
      simp [spectralKLPhysicalCompactDiv,hy]
    exact continuousAt_const.congr heq.symm

theorem spectralKLPhysicalCompactDiv_hasCompactSupport (f : ℝ → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (spectralKLPhysicalCompactDiv f) := by
  apply hfc.of_isClosed_subset (isClosed_tsupport _)
  simpa only [spectralKLPhysicalCompactDiv,div_eq_mul_inv] using!
    (tsupport_mul_subset_left : tsupport (fun x : ℝ => f x*((x : ℂ)⁻¹)) ⊆ tsupport f)

theorem spectralKLPhysicalCompactDiv_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable (spectralKLPhysicalCompactDiv f) :=
  (spectralKLPhysicalCompactDiv_continuous f hf hfp).integrable_of_hasCompactSupport
    (spectralKLPhysicalCompactDiv_hasCompactSupport f hfc)

theorem spectralKLPhysical_compact_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable f spectralKLPhysicalMeasure := by
  apply (spectralKLPositiveWeightMeasure_complex_integrable_iff (fun x => x⁻¹) f
    (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)).mpr
  apply (spectralKLPhysicalCompactDiv_integrable f hf hfc hfp).restrict.congr
  filter_upwards with x
  simp [spectralKLPhysicalCompactDiv,div_eq_mul_inv,mul_comm]

theorem spectralKLPhysical_compact_memLp (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    MemLp f 2 spectralKLPhysicalMeasure := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hC : Continuous (fun x : ℝ => ((‖f x‖^2 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (hf.norm.pow 2)
  have hs : tsupport (fun x : ℝ => ((‖f x‖^2 : ℝ) : ℂ)) ⊆ tsupport f := by
    unfold tsupport
    apply closure_mono
    intro x hx
    have hx' : ((‖f x‖^2 : ℝ) : ℂ) ≠ 0 := hx
    exact fun hf0 => hx' (by simp [hf0])
  have hS : HasCompactSupport (fun x : ℝ => ((‖f x‖^2 : ℝ) : ℂ)) :=
    hfc.of_isClosed_subset (isClosed_tsupport _) hs
  have hP : tsupport (fun x : ℝ => ((‖f x‖^2 : ℝ) : ℂ)) ⊆ Ioi (0 : ℝ) := hs.trans hfp
  have hi := (spectralKLPhysical_compact_integrable _ hC hS hP).re
  apply hi.congr
  filter_upwards with x
  change (((‖f x‖^2 : ℝ) : ℂ)).re = ‖f x‖^2
  rfl

theorem spectral_compact_positive_lower_bound (f : ℝ → ℂ) (hfc : HasCompactSupport f)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ tsupport f, a ≤ x := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨a,ha⟩ := hfc.exists_isLeast hs
    exact ⟨a,hfp ha.1,ha.2⟩
  · exact ⟨1,one_pos,fun x hx => (hs ⟨x,hx⟩).elim⟩

end ArtinMatthews
