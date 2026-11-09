module

public import ArtinMatthews.CubicTheta
public import OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
public import OAI.NumberTheory.DirichletL.Hecke.ThetaSeries
public import OAI.NumberTheory.DirichletL.Hecke.Coordinates
public import OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The six-unit normalization of the Eisenstein theta series

The lattice series counts all six associates of every nonzero ideal. The
constant lattice term is subtracted explicitly, so the statements apply even
to a principal residue character with nonzero value at the zero class.
-/
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths Complex UpperHalfPlane

namespace ArtinMatthews
open HeckeFamily

/-- The actual Eisenstein coordinate parametrization. -/
def thetaCoordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (ActualEisensteinCoordinates.unique_coordinates h).1
      (ActualEisensteinCoordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem theta_normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {thetaCoordinateEquiv n}) : ℝ) := by
  change EisensteinTheta.normForm n.1 n.2 =
    (Ideal.absNorm (Ideal.span {ActualEisensteinCoordinates.eval n.1 n.2}) : ℝ)
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ActualEisensteinCubic.eisEmbedding_eval_norm_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

/-- The summand indexed by an Eisenstein integer is invariant under its units. -/
def thetaElementTerm (χ : Character) (q : ℂ) (z : O) : ℂ :=
  thetaIdealCharacter χ (Ideal.span {z}) * q ^ (Ideal.span {z}).absNorm

@[simp] theorem thetaElementTerm_zero (χ : Character) (q : ℂ) :
    thetaElementTerm χ q 0 = 0 := by
  unfold thetaElementTerm
  rw [Ideal.span_singleton_eq_bot.mpr rfl]
  change thetaIdealCharacter χ 0 * q ^ Ideal.absNorm (0 : Ideal O) = 0
  rw [map_zero, zero_mul]

theorem thetaElementTerm_unit_mul (χ : Character) (q : ℂ) (u : Oˣ) (z : O) :
    thetaElementTerm χ q ((u : O) * z) = thetaElementTerm χ q z := by
  simp only [thetaElementTerm, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem thetaElementTerm_generator (χ : Character) (q : ℂ)
    (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    thetaElementTerm χ q (ConcretePrimeRowBridge.idealGenerator I.val) =
      thetaIdealCharacter χ I.val * q ^ I.val.absNorm := by
  simp only [thetaElementTerm, ConcretePrimeRowBridge.span_idealGenerator]

/-- The complex exponential at an imaginary point is the real Gaussian factor. -/
theorem theta_qParam_imaginary_pow (y : ℝ) (n : ℕ) :
    Function.Periodic.qParam 1 ((y : ℂ) * Complex.I) ^ n =
      (Real.exp (-2 * Real.pi * (n : ℝ) * y) : ℂ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  simp only [div_one]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Each nonzero lattice summand is the ideal-character Gaussian at its
principal ideal; the zero lattice term is removed. -/
theorem thetaElementTerm_coordinate (χ : Character) (y : ℝ) (n : ℤ × ℤ) :
    thetaElementTerm χ (Function.Periodic.qParam 1 ((y : ℂ) * Complex.I))
      (thetaCoordinateEquiv n) =
      if EisensteinTheta.normForm n.1 n.2 = 0 then 0 else
        HeckeTheta.periodicCoeff (coefficients χ) n *
          (Real.exp (-Real.pi * EisensteinTheta.normForm n.1 n.2 * (2 * y)) : ℂ) := by
  rw [theta_normForm_eq_absNorm_span]
  by_cases hz : thetaCoordinateEquiv n = 0
  · simp [hz]
  · have hnorm : (Ideal.span {thetaCoordinateEquiv n}).absNorm ≠ 0 := by
      intro hzero
      have hideal : Ideal.span {thetaCoordinateEquiv n} = 0 := Ideal.absNorm_eq_zero_iff.mp hzero
      exact hz (Ideal.span_singleton_eq_bot.mp hideal)
    rw [ite_eq_right (by exact_mod_cast hnorm), thetaElementTerm, thetaIdealCharacter_span χ hz,
      theta_qParam_imaginary_pow, periodicCoeff_eq_elementCoeff]
    change elementCoeff χ (coordinateElement n.1 n.2) * _ = _
    rw [show -2 * Real.pi * ((Ideal.span {thetaCoordinateEquiv n}).absNorm : ℝ) * y =
      -Real.pi * ((Ideal.span {thetaCoordinateEquiv n}).absNorm : ℝ) * (2 * y) by ring]

/-- Absolute convergence of the regularized element sum, with its exact
value supplied by the existing lattice theta construction. -/
theorem thetaElementTerm_hasSum (χ : Character) {y : ℝ} (hy : 0 < y) :
    HasSum (thetaElementTerm χ (Function.Periodic.qParam 1 ((y : ℂ) * Complex.I)))
      (HeckeTheta.theta (coefficients χ) (2 * y) - elementCoeff χ 0) := by
  apply thetaCoordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => thetaElementTerm χ
    (Function.Periodic.qParam 1 ((y : ℂ) * Complex.I)) (thetaCoordinateEquiv n)) _
  simp_rw [thetaElementTerm_coordinate]
  have hz : coefficients χ (0, 0) = elementCoeff χ 0 := by
    simp [coefficients, coordinateElement]
  have hs := HeckeTheta.theta_sub_zero_hasSum (coefficients χ) (show 0 < 2 * y by linarith)
  rw [HeckeTheta.pair_f₀, hz, ← HeckeTheta.theta_eq_pair (coefficients χ)
    (show 0 < 2 * y by linarith)] at hs
  exact hs

/-- The exact normalization connecting the staged lattice theta function to
the ideal theta series: six associates per ideal, and height scaling by two.
The possible zero lattice term is explicitly removed. -/
theorem latticeTheta_sub_zero_eq_six_heckeTheta (χ : Character)
    {y : ℝ} (hy : 0 < y) :
    HeckeTheta.theta (coefficients χ) (2 * y) - elementCoeff χ 0 =
      6 * heckeTheta χ ⟨(y : ℂ) * Complex.I, by simpa using hy⟩ := by
  let q := Function.Periodic.qParam 1 ((y : ℂ) * Complex.I)
  have hs := thetaElementTerm_hasSum χ hy
  have hunit := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (thetaElementTerm χ q) hs.summable (thetaElementTerm_zero χ q)
    (thetaElementTerm_unit_mul χ q)
  rw [hs.tsum_eq] at hunit
  simp_rw [thetaElementTerm_generator] at hunit
  have hnz : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal,
      thetaIdealCharacter χ I.val * q ^ I.val.absNorm) =
      ∑' I : Ideal O, thetaIdealCharacter χ I * q ^ I.absNorm := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun I : Ideal O => thetaIdealCharacter χ I * q ^ I.absNorm)
      (s := {I : Ideal O | I ≠ 0})
    intro I hI hzero
    exact hI (by simp only [hzero, thetaIdealCharacter_zero, zero_mul])
  rw [hnz] at hunit
  have hi := (heckeTheta_hasSum_ideals χ ⟨(y : ℂ) * Complex.I, by simpa using hy⟩).tsum_eq
  exact hunit.trans (congrArg (fun z : ℂ => 6 * z) hi)

/-- For the nonprincipal characters needed in the cubic argument, the lattice
constant is zero, and the ideal theta series is precisely one sixth of the
staged lattice theta at twice the imaginary height. -/
theorem heckeTheta_eq_normalized_lattice (χ : Character) (hχ : χ.residue ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    heckeTheta χ ⟨(y : ℂ) * Complex.I, by simpa using hy⟩ =
      HeckeTheta.theta (coefficients χ) (2 * y) / 6 := by
  have hz : elementCoeff χ 0 = 0 := by
    simpa [coefficients, coordinateElement] using
      HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ
  have h := latticeTheta_sub_zero_eq_six_heckeTheta χ hy
  rw [hz, sub_zero] at h
  rw [h]
  ring

end ArtinMatthews
