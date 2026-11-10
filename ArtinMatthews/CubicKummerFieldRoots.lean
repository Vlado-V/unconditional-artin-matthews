module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-!
# Concrete complex cube roots for the Kummer field

The primitive root of unity is explicit. Every two nonzero roots of the same
cubic differ by a power of this root, and complex conjugation preserves the
cubic equation with rational right-hand side.
-/

namespace ArtinMatthews

/-- The standard complex primitive cube root of unity. -/
noncomputable def cubicZeta : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

lemma cubicZeta_isPrimitiveRoot : IsPrimitiveRoot cubicZeta 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

@[simp] lemma cubicZeta_pow_three : cubicZeta ^ 3 = 1 :=
  cubicZeta_isPrimitiveRoot.pow_eq_one

lemma cubicZeta_ne_zero : cubicZeta ≠ 0 :=
  cubicZeta_isPrimitiveRoot.ne_zero (by norm_num)

@[simp] lemma conj_cubicZeta : star cubicZeta = cubicZeta⁻¹ :=
  (Complex.inv_eq_conj (cubicZeta_isPrimitiveRoot.norm'_eq_one (by norm_num))).symm

/-- Two nonzero roots of the same cubic have quotient a cube root of unity. -/
lemma cube_root_ratio_pow_three {z w : ℂ} (hw : w ≠ 0) (h : z ^ 3 = w ^ 3) :
    (z / w) ^ 3 = 1 := by
  rw [div_pow, h, div_self (pow_ne_zero _ hw)]

/-- The three roots of a nonzero cubic are the explicit root-of-unity multiples
of any one of its roots. -/
lemma cube_root_eq_zeta_pow_mul {z w : ℂ} (hw : w ≠ 0) (h : z ^ 3 = w ^ 3) :
    ∃ j < 3, z = cubicZeta ^ j * w := by
  obtain ⟨j, hj, hpow⟩ := cubicZeta_isPrimitiveRoot.eq_pow_of_pow_eq_one
    (cube_root_ratio_pow_three hw h)
  refine ⟨j, hj, ?_⟩
  rw [hpow, div_mul_cancel₀ _ hw]

/-- Conjugation fixes the cubic equation of any rational radicand. -/
lemma conj_cube_root_pow_three {a : ℚ} {z : ℂ} (hz : z ^ 3 = (a : ℂ)) :
    (star z) ^ 3 = (a : ℂ) := by
  simpa only [map_pow, map_ratCast, starRingEnd_apply] using congrArg (starRingEnd ℂ) hz

lemma conj_cube_root_ratio_pow_three {a : ℚ} {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ^ 3 = (a : ℂ)) :
    (star z / z) ^ 3 = 1 :=
  cube_root_ratio_pow_three hz0 ((conj_cube_root_pow_three hz).trans hz.symm)

lemma conj_cube_root_eq_zeta_pow_mul {a : ℚ} {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ^ 3 = (a : ℂ)) :
    ∃ j < 3, star z = cubicZeta ^ j * z :=
  cube_root_eq_zeta_pow_mul hz0 ((conj_cube_root_pow_three hz).trans hz.symm)

/-- Conjugation inverts every cube root of unity. -/
lemma conj_eq_inv_of_cube_eq_one {r : ℂ} (hr : r ^ 3 = 1) :
    star r = r⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hr (by norm_num))).symm

/-- The actual cubic cyclotomic field inside the complex numbers. -/
noncomputable def cubicCyclotomicField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {cubicZeta}

lemma cubicZeta_mem_cubicCyclotomicField : cubicZeta ∈ cubicCyclotomicField :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton cubicZeta)

instance cubicCyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension {3} ℚ cubicCyclotomicField :=
  (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    3 ℚ ℂ cubicCyclotomicField cubicZeta_isPrimitiveRoot).mpr rfl

/-- Every complex cube root of unity belongs to `ℚ(ζ₃)`. -/
lemma cube_unity_mem_cubicCyclotomicField {r : ℂ} (hr : r ^ 3 = 1) :
    r ∈ cubicCyclotomicField := by
  obtain ⟨j, _, hj⟩ := cubicZeta_isPrimitiveRoot.eq_pow_of_pow_eq_one hr
  rw [← hj]
  exact cubicCyclotomicField.pow_mem cubicZeta_mem_cubicCyclotomicField j

lemma cubicCyclotomicField_le_iff (K : IntermediateField ℚ ℂ) :
    cubicCyclotomicField ≤ K ↔ cubicZeta ∈ K := by
  rw [cubicCyclotomicField, IntermediateField.adjoin_le_iff]
  exact Set.singleton_subset_iff

end ArtinMatthews
