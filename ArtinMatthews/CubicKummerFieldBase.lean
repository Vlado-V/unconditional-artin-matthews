module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Galois.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# A concrete cubic splitting field inside the complex numbers

For a finite set of rational bases, adjoin all roots of the polynomial
`(X³ - 1) ∏ a ∈ S, (X³ - a)` inside `ℂ`. This is a genuine finite Galois
extension of `ℚ`: it is the splitting field in `ℂ` of the displayed polynomial.
The generator criterion identifies exactly the cube roots of the bases and
the cube roots of unity, without assuming any Kummer-theory conclusion.
-/

open Polynomial

namespace ArtinMatthews

/-- A polynomial whose splitting field is the cubic radical compositum. -/
noncomputable def cubicKummerPolynomial (S : Finset ℚ) : ℚ[X] :=
  (X ^ 3 - 1) * ∏ a ∈ S, (X ^ 3 - C a)

/-- The concrete cubic field, realized as an intermediate field of `ℂ / ℚ`. -/
noncomputable def cubicKummerField (S : Finset ℚ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((cubicKummerPolynomial S).rootSet ℂ)

lemma cubicKummerPolynomial_ne_zero (S : Finset ℚ) : cubicKummerPolynomial S ≠ 0 := by
  apply mul_ne_zero
  · simpa only [map_one] using (X_pow_sub_C_ne_zero (by norm_num : 0 < 3) (1 : ℚ))
  · apply Finset.prod_ne_zero_iff.mpr
    intro a _
    exact X_pow_sub_C_ne_zero (by norm_num) a

/-- Exactly the roots used to generate the concrete field. -/
theorem mem_cubicKummerPolynomial_rootSet_iff (S : Finset ℚ) (z : ℂ) :
    z ∈ (cubicKummerPolynomial S).rootSet ℂ ↔
      z ^ 3 = 1 ∨ ∃ a ∈ S, z ^ 3 = (a : ℂ) := by
  rw [Polynomial.mem_rootSet_of_ne (cubicKummerPolynomial_ne_zero S)]
  simp only [cubicKummerPolynomial, map_mul, map_sub, map_pow, map_one,
    aeval_X, map_prod, aeval_C, mul_eq_zero, sub_eq_zero, Finset.prod_eq_zero_iff]
  rfl

/-- Every cube root of unity belongs to the concrete field. -/
theorem cube_unity_mem_cubicKummerField (S : Finset ℚ) {z : ℂ} (hz : z ^ 3 = 1) :
    z ∈ cubicKummerField S :=
  IntermediateField.subset_adjoin ℚ _
    ((mem_cubicKummerPolynomial_rootSet_iff S z).mpr (Or.inl hz))

/-- Every complex cube root of a selected rational base belongs to the field. -/
theorem cube_root_mem_cubicKummerField {S : Finset ℚ} {a : ℚ} (ha : a ∈ S)
    {z : ℂ} (hz : z ^ 3 = (a : ℂ)) : z ∈ cubicKummerField S :=
  IntermediateField.subset_adjoin ℚ _
    ((mem_cubicKummerPolynomial_rootSet_iff S z).mpr (Or.inr ⟨a, ha, hz⟩))

/-- The concrete intermediate field is the splitting field of the displayed
rational polynomial, with the splitting inherited from algebraic closure of `ℂ`. -/
noncomputable instance cubicKummerField_isSplittingField (S : Finset ℚ) :
    IsSplittingField ℚ (cubicKummerField S) (cubicKummerPolynomial S) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

noncomputable instance cubicKummerField_finiteDimensional (S : Finset ℚ) :
    FiniteDimensional ℚ (cubicKummerField S) :=
  IsSplittingField.finiteDimensional (cubicKummerField S) (cubicKummerPolynomial S)

noncomputable instance cubicKummerField_normal (S : Finset ℚ) :
    Normal ℚ (cubicKummerField S) :=
  Normal.of_isSplittingField (cubicKummerPolynomial S)

/-- Separability follows from characteristic zero, and normality from splitting. -/
noncomputable instance cubicKummerField_isGalois (S : Finset ℚ) :
    IsGalois ℚ (cubicKummerField S) where

end ArtinMatthews
