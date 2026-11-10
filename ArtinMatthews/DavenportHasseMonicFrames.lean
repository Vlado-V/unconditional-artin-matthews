module

public import ArtinMatthews.DavenportHassePolynomialWeight
public import Mathlib.Algebra.Polynomial.OfFn


set_option backward.privateInPublic true
@[expose] public section

/-! A complete coefficient parametrization of monic polynomials.
This records the actual finite degree layers used by the polynomial
proof of Davenport--Hasse, including both boundary coefficients. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F]

def monicFrame (n : ℕ) (a : Fin n → F) : F[X] := X^n + Polynomial.ofFn n a

theorem monicFrame_coeff_lt (n : ℕ) (a : Fin n → F) (i : ℕ) (hi : i < n) :
    (monicFrame n a).coeff i = a ⟨i,hi⟩ := by
  simp only [monicFrame,coeff_add,coeff_X_pow,ite_eq_right (Nat.ne_of_lt hi),zero_add,
    Polynomial.ofFn_coeff_eq_val_of_lt a hi]

theorem monicFrame_coeff_self (n : ℕ) (a : Fin n → F) : (monicFrame n a).coeff n = 1 := by
  simp only [monicFrame,coeff_add,coeff_X_pow,ite_true,
    Polynomial.ofFn_coeff_eq_zero_of_ge a le_rfl,add_zero]

theorem monicFrame_coeff_gt (n : ℕ) (a : Fin n → F) (i : ℕ) (hi : n < i) :
    (monicFrame n a).coeff i = 0 := by
  simp only [monicFrame,coeff_add,coeff_X_pow,ite_eq_right (Nat.ne_of_gt hi),
    Polynomial.ofFn_coeff_eq_zero_of_ge a hi.le,add_zero]

theorem monicFrame_monic (n : ℕ) (a : Fin n → F) : (monicFrame n a).Monic :=
  monic_X_pow_add (Polynomial.ofFn_degree_lt a)

theorem monicFrame_natDegree (n : ℕ) (a : Fin n → F) : (monicFrame n a).natDegree = n := by
  rw [monicFrame,natDegree_add_eq_left_of_degree_lt]
  · exact natDegree_X_pow n
  · simpa only [degree_X_pow] using Polynomial.ofFn_degree_lt a

def monicCoefficientEquiv (n : ℕ) : MonicDegreeEq F n ≃ (Fin n → F) where
  toFun P i := P.1.coeff i
  invFun a := ⟨monicFrame n a,monicFrame_coeff_self n a,fun i hi => monicFrame_coeff_gt n a i hi⟩
  left_inv P := by
    apply Subtype.ext
    ext i
    by_cases hi : i < n
    · exact monicFrame_coeff_lt n _ i hi
    · by_cases he : i=n
      · subst i
        exact (monicFrame_coeff_self n _).trans P.2.1.symm
      · have hg : n < i := lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm he)
        exact (monicFrame_coeff_gt n _ i hg).trans (P.2.2 i hg).symm
  right_inv a := by
    funext i
    exact monicFrame_coeff_lt n a i i.2

theorem monicCoefficientEquiv_symm (n : ℕ) (a : Fin n → F) :
    ((monicCoefficientEquiv n).symm a).1 = monicFrame n a := rfl

theorem monicFrame_nextCoeff (n : ℕ) (a : Fin (n+1) → F) :
    (monicFrame (n+1) a).nextCoeff = a (Fin.last n) := by
  rw [nextCoeff_of_natDegree_pos (by rw [monicFrame_natDegree]; omega),monicFrame_natDegree]
  simpa only [Nat.add_sub_cancel,Fin.last] using monicFrame_coeff_lt (n+1) a n (by omega)

theorem monicFrame_weight (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (n : ℕ) (a : Fin (n+1) → F) :
    polynomialWeight χ ψ (monicFrame (n+1) a) =
      χ ((-1 : F)^(n+1)*a 0)*ψ (-a (Fin.last n)) := by
  rw [polynomialWeight,monicFrame_natDegree,monicFrame_nextCoeff,
    monicFrame_coeff_lt (n+1) a 0 (by omega)]
  rfl

def degreeCoefficient [Fintype F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (n : ℕ) : ℂ :=
  ∑ a : Fin n → F, polynomialWeight χ ψ (monicFrame n a)

theorem degreeCoefficient_monic_sum [Fintype F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (n : ℕ) :
    degreeCoefficient χ ψ n = ∑' P : MonicDegreeEq F n, polynomialWeight χ ψ P.1 := by
  have h := (monicCoefficientEquiv (F := F) n).symm.tsum_eq
    (fun P : MonicDegreeEq F n => polynomialWeight χ ψ P.1)
  simpa only [degreeCoefficient,tsum_fintype,monicCoefficientEquiv_symm] using h

end
end ArtinMatthews.DavenportHasse
