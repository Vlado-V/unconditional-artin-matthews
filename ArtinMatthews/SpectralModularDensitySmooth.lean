module

public import ArtinMatthews.SpectralModularDensitySmoothSpace
public import ArtinMatthews.SpectralModularBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth compact seeds supported in an open upper-half-plane set are dense
in its actual hyperbolic L² space. The proof uses test-function separation on
the real upper-half-plane manifold and Hilbert-space orthogonality. -/
noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported ContDiff Manifold
namespace ArtinMatthews

theorem h2SmoothSupportedLp_orthogonal_eq_zero (U : Set UpperHalfPlane) (hU : IsOpen U)
    (f : Lp ℂ 2 (volume.restrict U)) (hf : f ∈ (h2SmoothSupportedLp U)ᗮ) : f = 0 := by
  have hloc : LocallyIntegrableOn f U (volume.restrict U) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hzero : ∀ᵐ z ∂volume.restrict U, z ∈ U → f z = 0 := by
    apply hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, ℂ) hloc
    intro g hg hs hsupport
    let gC : UpperHalfPlane → ℂ := fun z => (g z : ℂ)
    have hgC : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ gC :=
      Complex.ofRealCLM.contMDiff.comp hg
    have hsC : HasCompactSupport gC := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have htC : tsupport gC ⊆ U := by
      apply Subset.trans (closure_mono ?_) hsupport
      intro z hz
      simpa [gC, Function.mem_support] using hz
    let ψ := h2SmoothCompactSeedOfContMDiff gC hgC hsC
    have hmem := ψ.val.continuous.memLp_of_hasCompactSupport ψ.val.hasCompactSupport
      (p:=2) (μ:=volume.restrict U)
    let y := hmem.toLp ψ.val
    have hy : y ∈ h2SmoothSupportedLp U := h2SmoothSupportedLp_mem U ψ htC
    have hinner : inner ℂ y f = 0 := ((h2SmoothSupportedLp U).mem_orthogonal f).mp hf y hy
    rw [L2.inner_def] at hinner
    calc
      (∫ z, g z • f z ∂volume.restrict U) =
          ∫ z, inner ℂ (y z) (f z) ∂volume.restrict U := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem] with z hz
        change y z = (g z : ℂ) at hz
        rw [hz]
        simp [Complex.real_smul, mul_comm]
      _ = 0 := hinner
  apply Lp.ext
  filter_upwards [hzero, ae_restrict_mem hU.measurableSet,
    Lp.coeFn_zero ℂ 2 (volume.restrict U)] with z hz hzu hz0
  exact (hz hzu).trans hz0.symm

theorem h2_smooth_compact_supported_dense (U : Set UpperHalfPlane) (hU : IsOpen U) :
    Dense {f : Lp ℂ 2 (volume.restrict U) | ∃ ψ : h2SmoothCompactSeeds,
      tsupport ψ.val ⊆ U ∧ f =ᵐ[volume.restrict U] ψ.val} := by
  change Dense (h2SmoothSupportedLp U : Set (Lp ℂ 2 (volume.restrict U)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  exact h2SmoothSupportedLp_orthogonal_eq_zero U hU f hf

theorem modular_smooth_compact_supported_dense :
    Dense {f : Lp ℂ 2 (volume.restrict ModularGroup.fd) | ∃ ψ : h2SmoothCompactSeeds,
      tsupport ψ.val ⊆ ModularGroup.fdo ∧ f =ᵐ[volume.restrict ModularGroup.fd] ψ.val} := by
  rw [modular_restrict_fd_eq_fdo]
  exact h2_smooth_compact_supported_dense ModularGroup.fdo ModularGroup.isOpen_fdo

end ArtinMatthews
