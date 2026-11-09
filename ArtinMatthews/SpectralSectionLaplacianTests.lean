module

public import ArtinMatthews.SpectralSectionLaplacian
public import ArtinMatthews.SpectralModularWeakTests


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth compact differential Laplacian test coefficients and
L² membership on every modular chart. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff MatrixGroups

namespace ArtinMatthews

theorem spectralPlanePositiveHyperbolic_contDiff (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (spectralPlanePositiveHyperbolic φ) := by
  have hh : ContDiff ℝ ∞ (fun p => ∑ i : Fin 2, spectralPlaneSecond φ i p) :=
    ContDiff.sum (fun i _ => spectralPlaneSecond_contDiff φ hφ i)
  exact (contDiff_snd.pow 2).smul hh.neg

theorem spectralPlanePositiveHyperbolic_tsupport_subset (φ : ℝ × ℝ → ℂ) :
    tsupport (spectralPlanePositiveHyperbolic φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hout
  have hd (i : Fin 2) : spectralPlaneSecond φ i p = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := spectralPlaneSecond φ i)
    intro ht
    exact hout ((tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i))
      ((tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i)) ht))
  exact hp (by simp only [spectralPlanePositiveHyperbolic,spectralPlanePositiveSecond,
    hd,Finset.sum_const_zero,neg_zero,smul_zero])

theorem spectralPlanePositiveHyperbolic_compact (φ : ℝ × ℝ → ℂ)
    (hs : HasCompactSupport φ) : HasCompactSupport (spectralPlanePositiveHyperbolic φ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (spectralPlanePositiveHyperbolic_tsupport_subset φ)

/-- A genuine compact smooth section's literal differential Laplacian is an
actual L² test on every chart; no independent integrability premise is used. -/
theorem h2SectionPositiveLaplacian_memLp_modular (r : SL(2, ℤ))
    (ψ : h2SmoothCompactSeeds) :
    MemLp (fun z : UpperHalfPlane => h2SectionPositiveLaplacian ψ.val (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  obtain ⟨_,_,φ,hφ,hc,_,_,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  have hlp := modularPlaneTest_memLp r (spectralPlanePositiveHyperbolic φ)
    (spectralPlanePositiveHyperbolic_contDiff φ hφ).continuous
    (spectralPlanePositiveHyperbolic_compact φ hc)
  apply MemLp.ae_eq _ hlp
  exact Eventually.of_forall (fun z =>
    (h2SectionPositiveLaplacian_representation ψ.val φ he (r⁻¹ • z)).symm)

end ArtinMatthews
