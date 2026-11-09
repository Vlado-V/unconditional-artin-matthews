module

public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import ArtinMatthews.SpectralCuspConstantTermEnergy
public import ArtinMatthews.SpectralCuspEulerRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Euler uniqueness for the actual completed constant term. The only
remaining equation in this interface is the explicitly displayed second
compact-test equation; the first derivative and both energy bounds are
proved for the actual operators. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTerm_zero_of_second_weak_equation
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (u : gamma0EnergySpace N)
    (hsecond : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) →
      (∫ y in Ioi (0 : ℝ), deriv (deriv ρ) y •
        gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u) y) =
      (∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) •
        gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u) y)) :
    gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  let c := gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
  let g := gamma0GlobalCuspConstantTermDerivative N r u
  have hfirst := gamma0GlobalCuspConstantTerm_weak_derivative N r u
  have hsecond' : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) →
      (∫ y in Ioi (0 : ℝ), deriv ρ y • g y) =
        -(∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) • c y) := by
    intro ρ hρ hρc hρs
    have hd : ContDiff ℝ ∞ (deriv ρ) := (contDiff_infty_iff_deriv.mp hρ).2
    have h := hfirst (deriv ρ) hd hρc.deriv (tsupport_deriv_subset.trans hρs)
    rw [hsecond ρ hρ hρc hρs] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  obtain ⟨C, G, _, _, hc, _, hC, hG⟩ := cuspWeakEuler_exists_classical c g
    (gamma0GlobalCuspConstantTerm_locallyIntegrable N r (gamma0EnergyInclusion N u))
    (gamma0GlobalCuspConstantTermDerivative_locallyIntegrable N r u) hfirst hsecond'
  exact (cuspEuler_vanishes_of_ae_quadratic_bound c C G hc.symm hC hG
    (gamma0GlobalCuspConstantTerm_integrable_energy N r (gamma0EnergyInclusion N u) 1 zero_lt_one)
    (fun Y hY hY1 => gamma0GlobalCuspConstantTerm_near_zero_energy N r
      (gamma0EnergyInclusion N u) Y hY hY1)).2

end ArtinMatthews
