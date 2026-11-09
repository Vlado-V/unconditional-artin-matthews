module

public import ArtinMatthews.SpectralSectionLaplacianTests


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact section coefficients as L² test vectors on the actual
modular domain, including the literal positive differential Laplacian. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem h2SmoothCompactSeed_memLp_modular (ψ : h2SmoothCompactSeeds) :
    MemLp ψ.val 2 (volume.restrict ModularGroup.fd) := by
  obtain ⟨_,_,φ,hφ,hc,_,_,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  have hlp := modularPlaneTest_memLp (1 : SL(2, ℤ)) φ hφ.continuous hc
  apply MemLp.ae_eq _ hlp
  apply Eventually.of_forall
  intro z
  simpa only [modularPlaneTest,inv_one,one_smul] using he z

theorem h2SectionPositiveLaplacian_memLp_fd (ψ : h2SmoothCompactSeeds) :
    MemLp (h2SectionPositiveLaplacian ψ.val) 2 (volume.restrict ModularGroup.fd) := by
  simpa only [inv_one,one_smul] using h2SectionPositiveLaplacian_memLp_modular (1 : SL(2, ℤ)) ψ

def modularSectionLp (ψ : h2SmoothCompactSeeds) : Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (h2SmoothCompactSeed_memLp_modular ψ).toLp ψ.val

def modularSectionLaplacianLp (ψ : h2SmoothCompactSeeds) : Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (h2SectionPositiveLaplacian_memLp_fd ψ).toLp (h2SectionPositiveLaplacian ψ.val)

theorem modularSectionLp_ae (ψ : h2SmoothCompactSeeds) :
    (modularSectionLp ψ : UpperHalfPlane → ℂ) =ᵐ[volume.restrict ModularGroup.fd] ψ.val :=
  (h2SmoothCompactSeed_memLp_modular ψ).coeFn_toLp

theorem modularSectionLaplacianLp_ae (ψ : h2SmoothCompactSeeds) :
    (modularSectionLaplacianLp ψ : UpperHalfPlane → ℂ) =ᵐ[volume.restrict ModularGroup.fd]
      h2SectionPositiveLaplacian ψ.val :=
  (h2SectionPositiveLaplacian_memLp_fd ψ).coeFn_toLp

end ArtinMatthews
