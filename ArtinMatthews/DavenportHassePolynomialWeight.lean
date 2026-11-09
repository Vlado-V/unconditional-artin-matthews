module

public import ArtinMatthews.FiniteFieldNormCharacter
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.NumberTheory.GaussSum


set_option backward.privateInPublic true
@[expose] public section

/-! The actual multiplicative polynomial weight in the elementary
Davenport--Hasse argument. Constant and next coefficients encode norm
and trace, and the linear polynomial sum is the genuine Gauss sum. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F]

def polynomialWeight (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (P : F[X]) : ℂ :=
  χ ((-1 : F)^P.natDegree * P.coeff 0) * ψ (-P.nextCoeff)

theorem polynomialWeight_one (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    polynomialWeight χ ψ 1 = 1 := by
  simp [polynomialWeight,Polynomial.nextCoeff]

theorem polynomialWeight_mul (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic) :
    polynomialWeight χ ψ (P*Q) = polynomialWeight χ ψ P * polynomialWeight χ ψ Q := by
  rw [polynomialWeight,hP.natDegree_mul hQ,hP.nextCoeff_mul hQ,mul_coeff_zero,pow_add,neg_add]
  have h : ((-1 : F)^P.natDegree * (-1)^Q.natDegree) * (P.coeff 0*Q.coeff 0) =
      ((-1 : F)^P.natDegree * P.coeff 0) * ((-1 : F)^Q.natDegree * Q.coeff 0) := by ring
  rw [h,map_mul,AddChar.map_add_eq_mul]
  unfold polynomialWeight
  ring

theorem polynomialWeight_pow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {P : F[X]} (hP : P.Monic) (n : ℕ) :
    polynomialWeight χ ψ (P^n) = polynomialWeight χ ψ P ^ n := by
  induction n with
  | zero => rw [pow_zero,polynomialWeight_one,pow_zero]
  | succ n ih => rw [pow_succ,polynomialWeight_mul χ ψ (hP.pow n) hP,ih,pow_succ]

theorem polynomialWeight_linear (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (a : F) :
    polynomialWeight χ ψ (X-C a) = χ a*ψ a := by
  simp only [polynomialWeight,natDegree_X_sub_C,pow_one,coeff_sub,coeff_X_zero,coeff_C_zero,
    zero_sub,neg_mul_neg,one_mul,nextCoeff_X_sub_C,neg_neg]

theorem polynomialWeight_linear_sum [Fintype F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (∑ a : F, polynomialWeight χ ψ (X-C a)) = gaussSum χ ψ := by
  simp only [polynomialWeight_linear,gaussSum]

theorem polynomialWeight_minpoly_powerBasis {E : Type*} [Field E] [Algebra F E]
    (b : PowerBasis F E) (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    polynomialWeight χ ψ (minpoly F b.gen) =
      χ (Algebra.norm F b.gen) * ψ (Algebra.trace F E b.gen) := by
  rw [polynomialWeight,Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    PowerBasis.trace_gen_eq_nextCoeff_minpoly,
    b.natDegree_minpoly]

end
end ArtinMatthews.DavenportHasse
