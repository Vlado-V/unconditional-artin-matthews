module

public import ArtinMatthews.SpectralGamma0EnergyPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual completed energy form localizes on normalized compact
interior tests to the literal selected-chart mass and Dirichlet integrals.
This identity is first proved on its genuine dense smooth generators. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0EnergyTest_local_pairing (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (ψ φ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo) :
    inner ℂ (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)) (gamma0EnergyTest N φ) =
      (∫ z in ModularGroup.fd, inner ℂ (ψ.val z) (gamma0PoincareSeed N φ.val (q.out⁻¹ • z))) +
      ∫ z in ModularGroup.fd, inner ℂ (h2SectionGradient ψ.val z)
        (h2SectionGradient (fun v => gamma0PoincareSeed N φ.val (q.out⁻¹ • v)) z) := by
  classical
  rw [gamma0EnergyTest_inner]
  rw [Finset.sum_eq_single q]
  · congr 1
    · apply integral_congr_ae
      filter_upwards [modular_fdo_ae_on_fd] with z hz
      rw [modularInteriorChartSeed_periodization_self N q.out ψ hψ hz]
    · apply integral_congr_ae
      filter_upwards [modular_fdo_ae_on_fd] with z hz
      exact modularInteriorChartSeed_gradient_pairing_self N q.out ψ hψ
        (gamma0PoincareSeed N φ.val) (gamma0PoincareSeed_smooth N φ.val φ.property) hz
  · intro t _ ht
    have hneq : (q.out : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ≠ t.out := by
      simpa only [Quotient.out_eq'] using Ne.symm ht
    have hm : (∫ z in ModularGroup.fd,
        inner ℂ (gamma0PoincareSeed N (modularInteriorChartSeed q.out ψ).val (t.out⁻¹ • z))
          (gamma0PoincareSeed N φ.val (t.out⁻¹ • z))) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [modular_fdo_ae_on_fd] with z hz
      have he := gamma0PoincareSeed_eq_zero_of_interior_chart_ne N _ q.out t.out
        (modularInteriorChartSeed_support q.out ψ hψ) hneq hz
      simp only [he,inner_zero_left,Pi.zero_apply]
    have hg : (∫ z in ModularGroup.fd,
        inner ℂ (h2SectionGradient (gamma0PoincareSeed N (modularInteriorChartSeed q.out ψ).val) (t.out⁻¹ • z))
          (h2SectionGradient (gamma0PoincareSeed N φ.val) (t.out⁻¹ • z))) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [modular_fdo_ae_on_fd] with z hz
      exact modularInteriorChartSeed_gradient_pairing_other N q.out t.out hneq ψ hψ
        (gamma0PoincareSeed N φ.val) (gamma0PoincareSeed_smooth N φ.val φ.property) hz
    rw [hm,hg,zero_add]
  · simp

end ArtinMatthews
