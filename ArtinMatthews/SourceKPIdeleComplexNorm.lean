module

public import ArtinMatthews.SourceKPAdelicWeylCharacter
public import Mathlib.Analysis.SpecialFunctions.Complex.Log


set_option backward.privateInPublic true
@[expose] public section

/-! The complex-parameter character of the actual normalized idele norm. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPIdeleComplexNorm (s : ℂ) : IdeleGroup (𝓞 K) K →* ℂˣ where
  toFun x := Units.mk0
    (Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K x) : ℂ)))
    (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    change Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K 1) : ℂ)) = 1
    rw [map_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  map_mul' x y := by
    apply Units.ext
    change Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K (x*y)) : ℂ)) =
      Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K x) : ℂ)) *
        Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K y) : ℂ))
    rw [map_mul, Real.log_mul (sourceKPIdeleAbsoluteNorm_pos K x).ne'
      (sourceKPIdeleAbsoluteNorm_pos K y).ne', Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sourceKPIdeleComplexNorm_coe (s : ℂ) (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPIdeleComplexNorm K s x : ℂˣ) : ℂ) =
      Complex.exp (s * (Real.log (sourceKPIdeleAbsoluteNorm K x) : ℂ)) := rfl

theorem sourceKPIdeleComplexNorm_add (s t : ℂ) (x : IdeleGroup (𝓞 K) K) :
    sourceKPIdeleComplexNorm K (s+t) x =
      sourceKPIdeleComplexNorm K s x * sourceKPIdeleComplexNorm K t x := by
  apply Units.ext
  simp only [sourceKPIdeleComplexNorm_coe, Units.val_mul, add_mul, Complex.exp_add]

theorem sourceKPIdeleComplexNorm_neg (s : ℂ) (x : IdeleGroup (𝓞 K) K) :
    sourceKPIdeleComplexNorm K (-s) x = (sourceKPIdeleComplexNorm K s x)⁻¹ := by
  apply Units.ext
  simp only [sourceKPIdeleComplexNorm_coe, Units.val_inv_eq_inv_val, neg_mul, Complex.exp_neg]

theorem sourceKPIdeleComplexNorm_principal (s : ℂ) (x : Kˣ) :
    sourceKPIdeleComplexNorm K s (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 := by
  apply Units.ext
  rw [sourceKPIdeleComplexNorm_coe, sourceKPIdeleAbsoluteNorm_principal,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Units.val_one]

theorem sourceKPIdeleComplexNorm_real (t : ℝ) (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPIdeleComplexNorm K (t : ℂ) x : ℂˣ) : ℂ) =
      ((sourceKPIdeleAbsoluteNorm K x) ^ t : ℝ) := by
  rw [sourceKPIdeleComplexNorm_coe,
    Real.rpow_def_of_pos (sourceKPIdeleAbsoluteNorm_pos K x), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem sourceKPIdeleComplexNorm_norm (s : ℂ) (x : IdeleGroup (𝓞 K) K) :
    ‖((sourceKPIdeleComplexNorm K s x : ℂˣ) : ℂ)‖ =
      (sourceKPIdeleAbsoluteNorm K x) ^ s.re := by
  rw [sourceKPIdeleComplexNorm_coe, Complex.norm_exp,
    Real.rpow_def_of_pos (sourceKPIdeleAbsoluteNorm_pos K x)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem sourceKPIdeleComplexNorm_sixth :
    sourceKPIdeleComplexNorm K (1/6 : ℂ) = sourceKPIdeleSixthNorm K := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  rw [sourceKPIdeleComplexNorm_coe, sourceKPIdeleSixthNorm_coe,
    Real.rpow_def_of_pos (sourceKPIdeleAbsoluteNorm_pos K x), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem sourceKPIdeleComplexNorm_cube (s : ℂ) (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPIdeleComplexNorm K s (x^3) : ℂˣ) : ℂ) =
      Complex.exp ((3*s) * (Real.log (sourceKPIdeleAbsoluteNorm K x) : ℂ)) := by
  rw [sourceKPIdeleComplexNorm_coe, map_pow, Real.log_pow, Complex.ofReal_mul]
  congr 1
  push_cast
  ring

end
end ArtinMatthews
