module

public import ArtinMatthews.VaryingKummerAnalyticMixedDeterminant
public import ArtinMatthews.VaryingKummerAnalyticMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian continuation for actual fractional-ideal lattices of arbitrary
number fields, including mixed signature. This is the lattice Mellin function;
the unit-orbit integral identifying a completed Dedekind zeta function remains
a separate theorem. No Dedekind or Hecke zero-free estimate is assumed here.

The generic Poisson and Mellin theorems are reused from OpenAI math-main,
OAI/NumberTheory/PrimePackets/{CoordinateLattices,LatticeTheta}.lean. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Gaussian sum over the actual elements of the fractional ideal. -/
def mixedIdealTheta (t : ℝ) : ℂ :=
  ∑' a : I.1, Complex.exp (-((Real.pi*t : ℝ) : ℂ) * ‖mixedIdealEmbedding K I a‖^2)

/-- The actual ideal sum is exactly the generic lattice theta sum. -/
theorem mixedIdealTheta_eq_normalizedTheta (t : ℝ) :
    mixedIdealTheta K I t = normalizedTheta (mixedIdealMatrix K I) t := by
  symm
  unfold normalizedTheta latticeTheta mixedIdealTheta
  have hnorm (z : MixedIdealIndex K I → ℤ) :
      ‖mixedIdealMatrix K I (euclideanInteger z)‖ =
        ‖mixedIdealEmbedding K I ((fractionalIdealBasis K I.1).equivFun.symm z)‖ :=
    mixedIdealMatrix_integer_norm K I z
  simp_rw [hnorm]
  exact (fractionalIdealBasis K I.1).equivFun.symm.toEquiv.tsum_eq
    (fun a : I.1 => Complex.exp (-((Real.pi*t : ℝ) : ℂ) * ‖mixedIdealEmbedding K I a‖^2))

/-- Poisson inversion for the actual ideal lattice, with its actual matrix dual. -/
theorem mixedIdealTheta_inversion {t : ℝ} (ht : 0 < t) :
    mixedIdealTheta K I t =
      ((|(LinearMap.det (mixedIdealMatrix K I).toLinearMap)⁻¹| : ℝ) : ℂ) *
      (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2)) *
      normalizedTheta (adjointEquiv (mixedIdealMatrix K I).symm) t⁻¹ := by
  rw [mixedIdealTheta_eq_normalizedTheta, normalizedTheta_inversion _ t ht,
    mixedIdealIndex_card]

/-- Poisson's coefficient is explicitly bound to ideal norm and field discriminant. -/
theorem mixedIdealTheta_inversion_discriminant {t : ℝ} (ht : 0 < t) :
    mixedIdealTheta K I t =
      (((((FractionalIdeal.absNorm I.1 : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)⁻¹) : ℝ) : ℂ) *
      (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2)) *
      normalizedTheta (adjointEquiv (mixedIdealMatrix K I).symm) t⁻¹ := by
  rw [mixedIdealTheta_inversion K I ht, abs_inv, mixedIdealMatrix_abs_det]

/-- The pole-subtracted Mellin continuation of the actual ideal lattice. -/
def mixedIdealThetaXi (s : ℂ) : ℂ := thetaMellinXi (mixedIdealMatrix K I) s

/-- This continuation is genuinely entire for mixed-signature number fields. -/
theorem mixedIdealThetaXi_entire : Differentiable ℂ (mixedIdealThetaXi K I) :=
  thetaMellinXi_differentiable _

/-- It agrees with the actual convergent ideal Gaussian Mellin transform. -/
theorem mixedIdealTheta_hasMellin {s : ℂ}
    (hs : (Module.finrank ℚ K : ℝ)/2 < s.re) :
    HasMellin (fun t => mixedIdealTheta K I t - 1) s
      (thetaMellinContinuation (mixedIdealMatrix K I) s) := by
  simp_rw [mixedIdealTheta_eq_normalizedTheta]
  apply normalizedTheta_hasMellin
  simpa only [mixedIdealIndex_card] using hs

/-- The functional equation has the full field degree and the actual dual lattice. -/
theorem mixedIdealThetaXi_functional_equation (s : ℂ) :
    mixedIdealThetaXi K I s =
      ((|(LinearMap.det (mixedIdealMatrix K I).toLinearMap)⁻¹| : ℝ) : ℂ) *
      thetaMellinXi (adjointEquiv (mixedIdealMatrix K I).symm)
        (((Module.finrank ℚ K : ℕ) : ℂ)/2 - s) := by
  unfold mixedIdealThetaXi
  rw [thetaMellinXi_functional_equation, mixedIdealIndex_card]

end
end ArtinMatthews.VaryingKummerAnalytic
