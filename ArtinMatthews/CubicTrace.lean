module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-!
# Finite cubic trace identities

These identities are algebraic: they do not assert any distribution statement
for Frobenius elements or primes.
-/

namespace ArtinMatthews

/-- The trace of a cubic character and its inverse character. -/
noncomputable def cubicTrace (z : ℂ) : ℂ := z + z⁻¹

/-- The complex-valued indicator that a cubic character is nontrivial. -/
noncomputable def cubicNontrivialIndicator (z : ℂ) : ℂ := if z ≠ 1 then 1 else 0

theorem cube_root_ne_zero {z : ℂ} (hz : z ^ 3 = 1) : z ≠ 0 := by
  intro hzero
  simp [hzero] at hz

@[simp] theorem cubicTrace_one : cubicTrace 1 = 2 := by
  norm_num [cubicTrace]

/-- Every nontrivial cube root has trace minus one. -/
theorem cubicTrace_eq_neg_one {z : ℂ} (hz : z ^ 3 = 1) (hne : z ≠ 1) :
    cubicTrace z = -1 := by
  have hzero := cube_root_ne_zero hz
  have hfactor : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      _ = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  have hpoly : z ^ 2 + z + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  unfold cubicTrace
  field_simp
  linear_combination hpoly

/-- Character nontriviality is a linear polynomial in its trace. -/
theorem cubicNontrivialIndicator_eq {z : ℂ} (hz : z ^ 3 = 1) :
    cubicNontrivialIndicator z = (2 - cubicTrace z) / 3 := by
  by_cases hne : z ≠ 1
  · rw [cubicNontrivialIndicator, ite_eq_left hne, cubicTrace_eq_neg_one hz hne]
    norm_num
  · have heq : z = 1 := not_ne_iff.mp hne
    subst z
    norm_num [cubicNontrivialIndicator]

/-- The cubic trace is invariant under inversion. -/
theorem cubicTrace_inv (z : ℂ) : cubicTrace z⁻¹ = cubicTrace z := by
  simp [cubicTrace, add_comm]

/-- The product of two traces is the sum of the product and quotient traces. -/
theorem cubicTrace_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    cubicTrace z * cubicTrace w = cubicTrace (z * w) + cubicTrace (z / w) := by
  unfold cubicTrace
  field_simp
  ring

theorem cubicTrace_mul_of_cube_eq_one {z w : ℂ} (hz : z ^ 3 = 1) (hw : w ^ 3 = 1) :
    cubicTrace z * cubicTrace w = cubicTrace (z * w) + cubicTrace (z / w) :=
  cubicTrace_mul (cube_root_ne_zero hz) (cube_root_ne_zero hw)

/-- The complex-valued indicator that both cubic characters are nontrivial. -/
noncomputable def cubicPairNontrivialIndicator (z w : ℂ) : ℂ :=
  if z ≠ 1 ∧ w ≠ 1 then 1 else 0

theorem cubicPairNontrivialIndicator_eq_product (z w : ℂ) :
    cubicPairNontrivialIndicator z w =
      cubicNontrivialIndicator z * cubicNontrivialIndicator w := by
  by_cases hz : z = 1 <;> by_cases hw : w = 1 <;>
    simp [cubicPairNontrivialIndicator, cubicNontrivialIndicator, hz, hw]

/-- The four nonconstant traces in the paper's two-character example. -/
theorem cubicPairNontrivialIndicator_eq {z w : ℂ} (hz : z ^ 3 = 1) (hw : w ^ 3 = 1) :
    cubicPairNontrivialIndicator z w =
      (4 - 2 * cubicTrace z - 2 * cubicTrace w +
        cubicTrace (z * w) + cubicTrace (z / w)) / 9 := by
  calc
    cubicPairNontrivialIndicator z w =
        cubicNontrivialIndicator z * cubicNontrivialIndicator w :=
      cubicPairNontrivialIndicator_eq_product z w
    _ = (4 - 2 * cubicTrace z - 2 * cubicTrace w + cubicTrace z * cubicTrace w) / 9 := by
      rw [cubicNontrivialIndicator_eq hz, cubicNontrivialIndicator_eq hw]
      ring
    _ = (4 - 2 * cubicTrace z - 2 * cubicTrace w +
        cubicTrace (z * w) + cubicTrace (z / w)) / 9 := by
      rw [cubicTrace_mul_of_cube_eq_one hz hw]
      ring

end ArtinMatthews
