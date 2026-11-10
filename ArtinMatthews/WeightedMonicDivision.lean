module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplication by a fixed monic divisor is a genuine equivalence of
monic degree layers. Its inverse is derived from divisibility and monic
cancellation, with no chosen factorization premise. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] {k n : ℕ}

abbrev DivisibleLayer (P : MonicDegreeEq F k) (n : ℕ) :=
  {Q : MonicDegreeEq F n // P.1 ∣ Q.1}

def quotient (P : MonicDegreeEq F k) (Q : DivisibleLayer P n) : MonicDegreeEq F (n-k) := by
  let R := Classical.choose Q.2
  have he : Q.1.1 = P.1*R := Classical.choose_spec Q.2
  have hR : R.Monic := P.monic.of_mul_monic_left (he ▸ Q.1.monic)
  have hd : k+R.natDegree = n := (P.natDegree ▸ (P.monic.natDegree_mul hR).symm).trans
    ((congrArg natDegree he.symm).trans Q.1.natDegree)
  exact MonicDegreeEq.mk R hR (by omega)

theorem quotient_mul (P : MonicDegreeEq F k) (Q : DivisibleLayer P n) :
    P.1*(quotient P Q).1 = Q.1.1 := (Classical.choose_spec Q.2).symm

def divisorEquiv (P : MonicDegreeEq F k) (hkn : k ≤ n) :
    MonicDegreeEq F (n-k) ≃ DivisibleLayer P n where
  toFun R := ⟨MonicDegreeEq.mk (P.1*R.1) (P.monic.mul R.monic) (by
    rw [P.monic.natDegree_mul R.monic,P.natDegree,R.natDegree]
    omega),⟨R.1,rfl⟩⟩
  invFun := quotient P
  left_inv R := by
    apply Subtype.ext
    apply mul_left_cancel₀ P.monic.ne_zero
    exact quotient_mul P _
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    exact quotient_mul P Q

theorem divisorEquiv_apply (P : MonicDegreeEq F k) (hkn : k ≤ n)
    (R : MonicDegreeEq F (n-k)) : ((divisorEquiv P hkn R).1 : F[X]) = P.1*R.1 := rfl

end
end ArtinMatthews.WeightedMonic
