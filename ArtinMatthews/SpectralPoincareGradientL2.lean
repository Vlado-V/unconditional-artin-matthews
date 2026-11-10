module

public import ArtinMatthews.SpectralSectionGradient
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralPoincareEnergy
public import ArtinMatthews.SpectralPoincareLinear
public import ArtinMatthews.SpectralPoincareSmooth
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Actual L² gradients of compact smooth arithmetic periodizations. -/

noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne]

theorem arithmeticPoincareGradient_memLp (ψ : h2SmoothCompactSeeds)
    (r : GL (Fin 2) ℝ) :
    MemLp (fun z : UpperHalfPlane =>
      h2SectionGradient (arithmeticPoincareSeed 𝒢 ψ.val) (r • z)) 2
      (volume.restrict ModularGroup.fd) := by
  have hm : AEStronglyMeasurable (fun z : UpperHalfPlane =>
      h2SectionGradient (arithmeticPoincareSeed 𝒢 ψ.val) (r • z))
      (volume.restrict ModularGroup.fd) := ((h2SectionGradient_continuous _
    (arithmeticPoincareSeed_smooth 𝒢 ψ.val ψ.property)).comp
      (continuous_const_smul r)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [IntegrableOn, h2SectionGradient_norm_sq] using
    arithmeticPoincareSeed_energy_integrable 𝒢 ψ r

def arithmeticPoincareGradientRegionLp (ψ : h2SmoothCompactSeeds) (r : GL (Fin 2) ℝ) :
    Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd) :=
  (arithmeticPoincareGradient_memLp 𝒢 ψ r).toLp _

theorem arithmeticPoincareGradientRegionLp_coeFn (ψ : h2SmoothCompactSeeds)
    (r : GL (Fin 2) ℝ) :
    (arithmeticPoincareGradientRegionLp 𝒢 ψ r : UpperHalfPlane → EuclideanSpace ℂ (Fin 2))
      =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => h2SectionGradient (arithmeticPoincareSeed 𝒢 ψ.val) (r • z)) :=
  (arithmeticPoincareGradient_memLp 𝒢 ψ r).coeFn_toLp

theorem arithmeticPoincareGradientRegionLp_norm_sq (ψ : h2SmoothCompactSeeds)
    (r : GL (Fin 2) ℝ) :
    ‖arithmeticPoincareGradientRegionLp 𝒢 ψ r‖ ^ 2 =
      ∫ z in ModularGroup.fd, h2SectionEnergy (arithmeticPoincareSeed 𝒢 ψ.val) (r • z) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [arithmeticPoincareGradientRegionLp_coeFn 𝒢 ψ r] with z hz
  rw [real_inner_self_eq_norm_sq, hz, h2SectionGradient_norm_sq]

private theorem poincare_gradient_add (ψ φ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    h2SectionGradient (arithmeticPoincareSeed 𝒢 (ψ + φ).val) z =
      h2SectionGradient (arithmeticPoincareSeed 𝒢 ψ.val) z +
      h2SectionGradient (arithmeticPoincareSeed 𝒢 φ.val) z := by
  change h2SectionGradient (arithmeticPoincareSeed 𝒢 (ψ.val + φ.val)) z = _
  rw [arithmeticPoincareSeed_add]
  exact h2SectionGradient_add _ _
    (arithmeticPoincareSeed_smooth 𝒢 ψ.val ψ.property)
    (arithmeticPoincareSeed_smooth 𝒢 φ.val φ.property) z

private theorem poincare_gradient_smul (c : ℂ) (ψ : h2SmoothCompactSeeds)
    (z : UpperHalfPlane) :
    h2SectionGradient (arithmeticPoincareSeed 𝒢 (c • ψ).val) z =
      c • h2SectionGradient (arithmeticPoincareSeed 𝒢 ψ.val) z := by
  change h2SectionGradient (arithmeticPoincareSeed 𝒢 (c • ψ.val)) z = _
  rw [arithmeticPoincareSeed_smul]
  exact h2SectionGradient_smul c _ (arithmeticPoincareSeed_smooth 𝒢 ψ.val ψ.property) z

/-- The actual gradient map is linear on genuine smooth seeds. -/
def arithmeticPoincareGradientRegionLinear (r : GL (Fin 2) ℝ) :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp (EuclideanSpace ℂ (Fin 2)) 2
      (volume.restrict ModularGroup.fd) where
  toFun ψ := arithmeticPoincareGradientRegionLp 𝒢 ψ r
  map_add' ψ φ := by
    apply Lp.ext
    filter_upwards [arithmeticPoincareGradientRegionLp_coeFn 𝒢 (ψ + φ) r,
      arithmeticPoincareGradientRegionLp_coeFn 𝒢 ψ r,
      arithmeticPoincareGradientRegionLp_coeFn 𝒢 φ r,
      Lp.coeFn_add (arithmeticPoincareGradientRegionLp 𝒢 ψ r)
        (arithmeticPoincareGradientRegionLp 𝒢 φ r)] with z hsum hψ hφ hadd
    rw [hadd]
    change _ = (arithmeticPoincareGradientRegionLp 𝒢 ψ r) z +
      (arithmeticPoincareGradientRegionLp 𝒢 φ r) z
    rw [hsum, hψ, hφ]
    exact poincare_gradient_add 𝒢 ψ φ _
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [arithmeticPoincareGradientRegionLp_coeFn 𝒢 (c • ψ) r,
      arithmeticPoincareGradientRegionLp_coeFn 𝒢 ψ r,
      Lp.coeFn_smul c (arithmeticPoincareGradientRegionLp 𝒢 ψ r)] with z hsmul hψ hmul
    simp only [RingHom.id_apply]
    rw [hmul]
    change _ = c • (arithmeticPoincareGradientRegionLp 𝒢 ψ r) z
    rw [hsmul, hψ]
    exact poincare_gradient_smul 𝒢 c ψ _

end ArtinMatthews
