module

public import ArtinMatthews.CubicThetaLattice
public import ArtinMatthews.CubicThetaTransform


set_option backward.privateInPublic true
@[expose] public section

/-!
# The ideal theta series as a holomorphic lattice sum

The six-unit comparison holds throughout the upper half plane. In particular,
for a nonprincipal residue character the actual ideal theta series is exactly
one sixth of the periodic character-weighted complex Gaussian sum. This is an
identity of convergent series, not a modularity assumption.
-/
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths Complex UpperHalfPlane

namespace ArtinMatthews
open HeckeFamily

/-- Exponentiation of the nome agrees with the Eisenstein complex Gaussian
under the actual coordinate parametrization. -/
theorem theta_qParam_coordinate_pow (τ : ℍ) (n : ℤ × ℤ) :
    Function.Periodic.qParam 1 (τ : ℂ) ^
        (Ideal.span {thetaCoordinateEquiv n}).absNorm =
      eisensteinComplexGaussian (eisensteinGaussianParameter τ) n := by
  have hn := congrArg (fun x : ℝ => (x : ℂ)) (theta_normForm_eq_absNorm_span n)
  simp only [EisensteinTheta.normForm, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast,
    Complex.ofReal_natCast] at hn
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  unfold eisensteinComplexGaussian eisensteinGaussianParameter
  rw [hn]
  congr 1
  norm_num
  ring

/-- Absolute convergence of the Eisenstein-element series at every point of
the upper half plane. -/
theorem thetaElementTerm_summable (χ : Character) (τ : ℍ) :
    Summable (thetaElementTerm χ (Function.Periodic.qParam 1 (τ : ℂ))) := by
  apply thetaCoordinateEquiv.summable_iff.mp
  have hs := (eisensteinComplexGaussian_summable
    (eisensteinGaussianParameter_re τ)).norm
  apply hs.of_norm_bounded
  intro n
  change ‖thetaIdealCharacter χ (Ideal.span {thetaCoordinateEquiv n}) *
    Function.Periodic.qParam 1 (τ : ℂ) ^
      (Ideal.span {thetaCoordinateEquiv n}).absNorm‖ ≤ _
  rw [theta_qParam_coordinate_pow, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (thetaIdealCharacter_norm_le_one χ _)

/-- The complete complex Gaussian identity, with the zero term handled by
the actual ideal character's zero extension. -/
theorem latticeIdealGaussian_eq_six_heckeTheta (χ : Character) (τ : ℍ) :
    (∑' n : ℤ × ℤ, thetaIdealCharacter χ (Ideal.span {thetaCoordinateEquiv n}) *
      eisensteinComplexGaussian (eisensteinGaussianParameter τ) n) =
        6 * heckeTheta χ τ := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hunit := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (thetaElementTerm χ q) (thetaElementTerm_summable χ τ)
    (thetaElementTerm_zero χ q) (thetaElementTerm_unit_mul χ q)
  simp_rw [thetaElementTerm_generator] at hunit
  have hnz : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal,
      thetaIdealCharacter χ I.val * q ^ I.val.absNorm) =
      ∑' I : Ideal O, thetaIdealCharacter χ I * q ^ I.absNorm := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun I : Ideal O => thetaIdealCharacter χ I * q ^ I.absNorm)
      (s := {I : Ideal O | I ≠ 0})
    intro I hI hzero
    exact hI (by simp only [hzero, thetaIdealCharacter_zero, zero_mul])
  rw [hnz, (heckeTheta_hasSum_ideals χ τ).tsum_eq] at hunit
  rw [← hunit, ← thetaCoordinateEquiv.tsum_eq (thetaElementTerm χ q)]
  apply tsum_congr
  intro n
  simp only [thetaElementTerm, q, theta_qParam_coordinate_pow]

/-- Nonprincipal residue characters vanish at the zero element. -/
theorem thetaElementCoeff_zero_of_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    elementCoeff χ 0 = 0 := by
  simpa [coefficients, coordinateElement] using
    HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ

/-- The actual ideal character equals the periodic residue weight at every
lattice point for a nonprincipal character, including the origin. -/
theorem thetaIdealCharacter_coordinate_of_nonprincipal (χ : Character)
    (hχ : χ.residue ≠ 1) (n : ℤ × ℤ) :
    thetaIdealCharacter χ (Ideal.span {thetaCoordinateEquiv n}) =
      HeckeTheta.periodicCoeff (coefficients χ) n := by
  rw [periodicCoeff_eq_elementCoeff]
  change thetaIdealCharacter χ (Ideal.span {thetaCoordinateEquiv n}) =
    elementCoeff χ (thetaCoordinateEquiv n)
  by_cases hz : thetaCoordinateEquiv n = 0
  · rw [hz, Ideal.span_singleton_eq_bot.mpr rfl]
    exact (thetaIdealCharacter_zero χ).trans
      (thetaElementCoeff_zero_of_nonprincipal χ hχ).symm
  · exact thetaIdealCharacter_span χ hz

/-- The ideal theta function agrees with the genuine periodic
character-weighted complex Gaussian sum throughout the upper half plane. -/
theorem periodicGaussian_eq_six_heckeTheta (χ : Character)
    (hχ : χ.residue ≠ 1) (τ : ℍ) :
    (∑' n : ℤ × ℤ, HeckeTheta.periodicCoeff (coefficients χ) n *
      eisensteinComplexGaussian (eisensteinGaussianParameter τ) n) =
        6 * heckeTheta χ τ := by
  simpa only [thetaIdealCharacter_coordinate_of_nonprincipal χ hχ] using
    latticeIdealGaussian_eq_six_heckeTheta χ τ

end ArtinMatthews
