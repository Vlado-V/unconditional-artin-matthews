module

public import ArtinMatthews.SpectralKLCompactFubini


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact physical/spectral adjoint identity, retaining both
literal weighted measures and the real K kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKL_compact_adjoint (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (g : spectralKLTestSubmodule) :
    inner ℂ (spectralKLTestSynthesis g) ((spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f) =
      ∫ t : ℝ, (starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure := by
  let G : ℝ → ℂ := fun t => (starRingEnd ℂ) ((spectralKLPlancherelWeight t : ℂ)*g.val t)
  have hG : Continuous G := by
    exact Complex.continuous_conj.comp
      ((Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul g.property.1.continuous)
  have hGc : HasCompactSupport G :=
    (g.property.2.1.mul_left).comp_left (map_zero (starRingEnd ℂ))
  have hGeq (x : ℝ) (hx : 0 < x) :
      (starRingEnd ℂ) (spectralKLWeightedSynthesis g x) = spectralKLSynthesis G x := by
    rw [spectralKLWeightedSynthesis_eq g g.property.2.2 hx]
    exact (spectralKLSynthesis_conj _ x).symm
  have hinner :
      inner ℂ (spectralKLTestSynthesis g) ((spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f) =
        ∫ x : ℝ, f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x) ∂spectralKLPhysicalMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [spectralKLTestSynthesis_coe g,
      (spectralKLPhysical_compact_memLp f hf hfc hfp).coeFn_toLp] with x hS hF
    rw [RCLike.inner_apply,hS,hF]
  have hphys :
      (∫ x : ℝ, f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x) ∂spectralKLPhysicalMeasure) =
        ∫ x in Ioi (0 : ℝ), (x⁻¹ : ℝ)* (f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x)) :=
    spectralKLPositiveWeightMeasure_complex_integral _ _ (by fun_prop)
      (fun x hx => inv_nonneg.mpr hx.le)
  have hspec :
      (∫ t : ℝ, (starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure) =
        ∫ t in Ioi (0 : ℝ), (spectralKLPlancherelWeight t : ℂ)*
          ((starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t) :=
    spectralKLPositiveWeightMeasure_complex_integral _ _ spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)
  rw [hinner,hphys,hspec]
  calc
    _ = ∫ x in Ioi (0 : ℝ), spectralKLSynthesis G x*spectralKLPhysicalCompactDiv f x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [hGeq x hx]
      simp only [spectralKLPhysicalCompactDiv,Complex.ofReal_inv,div_eq_mul_inv]
      ring
    _ = ∫ x : ℝ, spectralKLSynthesis G x*spectralKLPhysicalCompactDiv f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hfp h))
      simp [spectralKLPhysicalCompactDiv,hf0]
    _ = ∫ t : ℝ, G t*spectralKLPhysicalAnalysisIntegral f t :=
      spectralKL_compact_fubini f G hf hfc hfp hG hGc
    _ = ∫ t in Ioi (0 : ℝ), G t*spectralKLPhysicalAnalysisIntegral f t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g.val t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (g.property.2.2 h))
      simp [G,hg0]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [G,map_mul,Complex.conj_ofReal]
      ring

end ArtinMatthews
