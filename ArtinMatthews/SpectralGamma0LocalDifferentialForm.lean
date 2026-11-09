module

public import ArtinMatthews.SpectralGamma0LocalForm
public import ArtinMatthews.SpectralSectionModularGreen
public import ArtinMatthews.SpectralSectionModularTests
public import ArtinMatthews.SpectralModularWeakFunctionals


set_option backward.privateInPublic true
@[expose] public section

/-! The literal coordinate mass-plus-Laplacian form for a compact interior
test, first on genuine periodizations and then on every completed energy
vector. The extension uses actual bounded L² test functionals. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0EnergyTest_local_differential_pairing (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (ψ φ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo) :
    inner ℂ (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)) (gamma0EnergyTest N φ) =
      (∫ z in ModularGroup.fd, inner ℂ (ψ.val z) (gamma0PoincareSeed N φ.val (q.out⁻¹ • z))) +
      ∫ z in ModularGroup.fd, inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        (gamma0PoincareSeed N φ.val (q.out⁻¹ • z)) := by
  rw [gamma0EnergyTest_local_pairing N q ψ φ hψ]
  congr 1
  symm
  apply h2Section_modular_complex_green ψ (hψ.trans ModularGroup.fdo_subset_fd)
  exact spectralSection_smooth_pullback (gamma0PoincareSeed N φ.val)
    (gamma0PoincareSeed_smooth N φ.val φ.property)
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹) (by simp)

theorem gamma0Energy_completed_local_differential_pairing (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (u : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)) u =
      (∫ z in ModularGroup.fd, inner ℂ (ψ.val z) ((gamma0EnergyMassChart N q u) z)) +
      ∫ z in ModularGroup.fd, inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        ((gamma0EnergyMassChart N q u) z) := by
  let A := innerSL ℂ (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))
  let B := (innerSL ℂ (modularSectionLp ψ)).comp (gamma0EnergyMassChart N q) +
    (innerSL ℂ (modularSectionLaplacianLp ψ)).comp (gamma0EnergyMassChart N q)
  have hB (v : gamma0EnergySpace N) : B v =
      (∫ z in ModularGroup.fd, inner ℂ (ψ.val z) ((gamma0EnergyMassChart N q v) z)) +
      ∫ z in ModularGroup.fd, inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        ((gamma0EnergyMassChart N q v) z) := by
    change inner ℂ (modularSectionLp ψ) (gamma0EnergyMassChart N q v) +
      inner ℂ (modularSectionLaplacianLp ψ) (gamma0EnergyMassChart N q v) = _
    rw [L2.inner_def,L2.inner_def]
    congr 1
    · apply integral_congr_ae
      filter_upwards [modularSectionLp_ae ψ] with z hz
      rw [hz]
    · apply integral_congr_ae
      filter_upwards [modularSectionLaplacianLp_ae ψ] with z hz
      rw [hz]
  have hall : ∀ v : gamma0EnergySpace N, A v = B v := by
    apply isClosed_property (gamma0EnergyTest_dense N) (isClosed_eq A.continuous B.continuous)
    intro φ
    change inner ℂ (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)) (gamma0EnergyTest N φ) = B (gamma0EnergyTest N φ)
    rw [hB,gamma0EnergyTest_local_differential_pairing N q ψ φ hψ]
    congr 1
    · apply integral_congr_ae
      filter_upwards [gamma0EnergyMassChart_test_ae N q φ] with z hz
      rw [hz]
    · apply integral_congr_ae
      filter_upwards [gamma0EnergyMassChart_test_ae N q φ] with z hz
      rw [hz]
  exact (hall u).trans (hB u)

end ArtinMatthews
