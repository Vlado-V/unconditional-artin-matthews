module

public import ArtinMatthews.CubicThetaActualCuspFormBase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact comparison of the proved theta level with the specified Hecke
residue modulus. No minimal-conductor or newform assertion is made. -/
namespace ArtinMatthews

/-- The explicit compatible level is eight times three times the norm of
the specified residue modulus `(9 A)`. -/
theorem cubicNumeratorThetaLevel_eq_modulusNorm (A : ℤ) (hA : A ≠ 0) :
    cubicNumeratorThetaLevel A =
      8 * (3 * (cubicNumeratorHeckeCharacter A hA).modulus.absNorm) := by
  rw [cubicNumeratorThetaLevel_eq, cubicNumeratorHeckeCharacter_modulus_absNorm]
  ring

theorem cubicNumeratorTheta_modulusNorm_three_dvd_level (A : ℤ) (hA : A ≠ 0) :
    3 * (cubicNumeratorHeckeCharacter A hA).modulus.absNorm ∣
      cubicNumeratorThetaLevel A := by
  rw [cubicNumeratorThetaLevel_eq_modulusNorm A hA]
  exact dvd_mul_left _ _

end ArtinMatthews
