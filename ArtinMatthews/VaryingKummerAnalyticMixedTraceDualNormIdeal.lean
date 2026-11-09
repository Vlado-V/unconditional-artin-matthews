module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.FractionalIdeal.Norm


set_option backward.privateInPublic true
@[expose] public section

/-! Exact norm of the trace-dual fractional ideal in an arbitrary number
field, including fields with complex places. -/
noncomputable section
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The trace dual is the inverse different times the inverse ideal. -/
theorem mixedTraceDualIdeal_eq_inv_different_mul_inv :
    (mixedTraceDualIdeal K I).1 =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * I.1⁻¹ := by
  change FractionalIdeal.dual ℤ ℚ I.1 = _
  rw [FractionalIdeal.dual_eq_mul_inv,
    coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

/-- The exact rational norm, with the absolute discriminant in natural form. -/
theorem mixedTraceDualIdeal_absNorm_rat :
    FractionalIdeal.absNorm (mixedTraceDualIdeal K I).1 =
      (((NumberField.discr K).natAbs : ℚ) * FractionalIdeal.absNorm I.1)⁻¹ := by
  rw [mixedTraceDualIdeal_eq_inv_different_mul_inv, map_mul, map_inv₀, map_inv₀,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal K (𝓞 K), mul_inv]

/-- The exact real norm formula, in the normalization of the mixed-signature
functional equation. -/
theorem mixedTraceDualIdeal_absNorm :
    (FractionalIdeal.absNorm (mixedTraceDualIdeal K I).1 : ℝ) =
      (|(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm I.1 : ℝ))⁻¹ := by
  have h := mixedTraceDualIdeal_absNorm_rat K I
  have hcast : ((NumberField.discr K).natAbs : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hh := congrArg (fun x : ℚ => (x : ℝ)) h
  push_cast at hh
  rwa [hcast] at hh

/-- The equivalent reciprocal-product expression. -/
theorem mixedTraceDualIdeal_absNorm_div :
    (FractionalIdeal.absNorm (mixedTraceDualIdeal K I).1 : ℝ) =
      1 / (|(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm I.1 : ℝ)) := by
  rw [mixedTraceDualIdeal_absNorm, one_div]

end ArtinMatthews.VaryingKummerAnalytic
