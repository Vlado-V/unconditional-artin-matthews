module

public import ArtinMatthews.CubicThetaTransform
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit scalar transformations of the unweighted Eisenstein theta.
These are derived from its proved Poisson formula and integer periodicity. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane
open scoped MatrixGroups

/-- Integer translation fixes the actual unweighted Eisenstein theta. -/
theorem eisensteinHolomorphicTheta_int_translate (n : ℤ) (τ : ℍ) :
    eisensteinHolomorphicTheta ((n : ℝ) +ᵥ τ) = eisensteinHolomorphicTheta τ := by
  unfold eisensteinHolomorphicTheta
  apply tsum_congr
  intro z
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n * (z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2), ?_⟩
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast]
  push_cast
  ring

/-- The lower unipotent matrix with parameter divisible by three. -/
def eisensteinLowerUnipotent (n : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; 3 * n, 1], by simp [Matrix.det_fin_two]⟩

/-- The lower unipotent action is two Fricke maps with an integer translation. -/
theorem eisensteinLowerUnipotent_fricke (n : ℤ) (τ : ℍ) :
    eisensteinLowerUnipotent n • τ =
      eisensteinFricke ((-(n : ℝ)) +ᵥ eisensteinFricke τ) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hcast (z : ℤ) : ((algebraMap ℤ ℝ z : ℝ) : ℂ) = (z : ℂ) := by simp
  simp only [hcast]
  simp [eisensteinLowerUnipotent, eisensteinFricke, UpperHalfPlane.coe_vadd]
  field_simp [τ.ne_zero]
  ring_nf
  rw [show (-1 - (τ : ℂ) * (n : ℂ) * 3) = -(1 + (τ : ℂ) * (n : ℂ) * 3) by ring,
    inv_neg, neg_neg]

/-- The scalar multiplier for every lower unipotent of level three is
exactly the classical weight-one factor. -/
theorem eisensteinHolomorphicTheta_lowerUnipotent (n : ℤ) (τ : ℍ) :
    eisensteinHolomorphicTheta (eisensteinLowerUnipotent n • τ) =
      ((3 * n : ℂ) * τ + 1) * eisensteinHolomorphicTheta τ := by
  rw [eisensteinLowerUnipotent_fricke, eisensteinHolomorphicTheta_fricke]
  have ht := eisensteinHolomorphicTheta_int_translate (-n) (eisensteinFricke τ)
  simp only [Int.cast_neg] at ht
  rw [ht, eisensteinHolomorphicTheta_fricke]
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [UpperHalfPlane.coe_vadd]
  simp only [eisensteinFricke]
  change (-Complex.I * (Real.sqrt 3 : ℂ) * (((-(n : ℝ) : ℝ) : ℂ) + (-1 / (3 * (τ : ℂ))))) *
    ((-Complex.I * (Real.sqrt 3 : ℂ) * (τ : ℂ)) * eisensteinHolomorphicTheta τ) = _
  push_cast
  field_simp [τ.ne_zero]
  simp only [Complex.I_sq] at *
  linear_combination (3 * (τ : ℂ) * (n : ℂ) + 1) * eisensteinHolomorphicTheta τ * hs

end ArtinMatthews
