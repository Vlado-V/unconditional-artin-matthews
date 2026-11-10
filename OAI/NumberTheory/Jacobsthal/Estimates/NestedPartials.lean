module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem nestedX_partial_zero (Q : MV R) :
    nestedX R (MvPolynomial.pderiv 0 Q) = (nestedX R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

theorem nestedY_partial_one (Q : MV R) :
    nestedY R (MvPolynomial.pderiv 1 Q) = (nestedY R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

end ErdosCriticalGeometry

end

end Erdos970

end OAI
