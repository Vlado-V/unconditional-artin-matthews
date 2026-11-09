module

public import ArtinMatthews.KummerSplittingInertia
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.KummerExtension


set_option backward.privateInPublic true
@[expose] public section

/-! The actual auxiliary cyclotomic compositum from the splitting argument:
F_q = ℚ(ζ_(12q)) and K̃_q = F_q(a^(1/q)) inside ℂ. -/

set_option maxHeartbeats 800000

noncomputable section
namespace ArtinMatthews

/-- Scalar compatibility of the actual inclusion of intermediate fields. -/
theorem intermediateField_inclusion_scalarTower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) (h : K ≤ L) :
    let : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
    IsScalarTower F K L := by
  let : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion h).comp_algebraMap.symm

/-- The exact auxiliary cyclotomic field from the paper. -/
def twelfthCyclotomicField (q : ℕ) : IntermediateField ℚ ℂ :=
  primeCyclotomicField (12 * q)

/-- The actual radical extension over the auxiliary cyclotomic field. -/
def twelfthKummerField (q : ℕ) (a : ℤ) : IntermediateField ℚ ℂ :=
  (IntermediateField.adjoin (twelfthCyclotomicField q) {primeRadicalRoot q a}).restrictScalars ℚ

instance twelfthCyclotomicField_isCyclotomicExtension (q : ℕ) [NeZero q] :
    IsCyclotomicExtension {12 * q} ℚ (twelfthCyclotomicField q) := by
  let : NeZero (12 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
  exact primeCyclotomicField_isCyclotomicExtension (12 * q)

instance twelfthCyclotomicField_finiteDimensional (q : ℕ) [NeZero q] :
    FiniteDimensional ℚ (twelfthCyclotomicField q) :=
  IsCyclotomicExtension.finite_of_singleton (12 * q) ℚ _

instance twelfthCyclotomicField_isGalois (q : ℕ) [NeZero q] :
    IsGalois ℚ (twelfthCyclotomicField q) :=
  IsCyclotomicExtension.isGalois {12 * q} ℚ _

instance twelfthCyclotomicField_isAbelianGalois (q : ℕ) [NeZero q] :
    IsAbelianGalois ℚ (twelfthCyclotomicField q) := by
  let : IsMulCommutative Gal(twelfthCyclotomicField q/ℚ) :=
    IsCyclotomicExtension.isMulCommutative {12 * q} ℚ _
  exact {}

theorem primeCyclotomicField_le_twelfthCyclotomicField (q : ℕ) [NeZero q] :
    primeCyclotomicField q ≤ twelfthCyclotomicField q := by
  apply (primeCyclotomicField_le_iff q _).mpr
  apply root_of_unity_mem_primeCyclotomicField (Nat.mul_pos (by decide) (NeZero.pos q))
  rw [Nat.mul_comm 12 q, pow_mul, primeCyclotomicRoot_pow (NeZero.pos q), one_pow]

theorem twelveCyclotomicField_le_twelfthCyclotomicField (q : ℕ) [NeZero q] :
    primeCyclotomicField 12 ≤ twelfthCyclotomicField q := by
  apply (primeCyclotomicField_le_iff 12 _).mpr
  apply root_of_unity_mem_primeCyclotomicField (Nat.mul_pos (by decide) (NeZero.pos q))
  rw [pow_mul, primeCyclotomicRoot_pow (by decide : 0 < 12), one_pow]

/-- This is the compositum with the original Kummer field, literally as
intermediate fields of the same complex overfield. -/
theorem twelfthKummerField_eq_sup (q : ℕ) (a : ℤ) [NeZero q] :
    twelfthKummerField q a = twelfthCyclotomicField q ⊔ primeKummerField q a := by
  rw [twelfthKummerField, IntermediateField.restrictScalars_adjoin_eq_sup,
    primeKummerField_eq_adjoin, IntermediateField.adjoin_union]
  have hle := primeCyclotomicField_le_twelfthCyclotomicField q
  change _ = twelfthCyclotomicField q ⊔
    (primeCyclotomicField q ⊔ IntermediateField.adjoin ℚ {primeRadicalRoot q a})
  rw [← sup_assoc, sup_eq_left.mpr hle]

theorem primeKummerField_le_twelfthKummerField (q : ℕ) (a : ℤ) [NeZero q] :
    primeKummerField q a ≤ twelfthKummerField q a := by
  rw [twelfthKummerField_eq_sup]
  exact le_sup_right

instance twelfthKummerField_algebra_cyclotomic (q : ℕ) (a : ℤ) :
    Algebra (twelfthCyclotomicField q) (twelfthKummerField q a) :=
  inferInstanceAs (Algebra (twelfthCyclotomicField q)
    (IntermediateField.adjoin (twelfthCyclotomicField q) {primeRadicalRoot q a}))

instance twelfthKummerField_scalarTower_cyclotomic (q : ℕ) (a : ℤ) :
    IsScalarTower ℚ (twelfthCyclotomicField q) (twelfthKummerField q a) :=
  inferInstanceAs (IsScalarTower ℚ (twelfthCyclotomicField q)
    (IntermediateField.adjoin (twelfthCyclotomicField q) {primeRadicalRoot q a}))

instance twelfthKummerField_algebra_kummer (q : ℕ) (a : ℤ) [NeZero q] :
    Algebra (primeKummerField q a) (twelfthKummerField q a) :=
  (IntermediateField.inclusion (primeKummerField_le_twelfthKummerField q a)).toRingHom.toAlgebra

instance twelfthKummerField_scalarTower_kummer (q : ℕ) (a : ℤ) [NeZero q] :
    IsScalarTower ℚ (primeKummerField q a) (twelfthKummerField q a) :=
  intermediateField_inclusion_scalarTower (primeKummerField q a) (twelfthKummerField q a)
    (primeKummerField_le_twelfthKummerField q a)

instance twelfthKummerField_finiteDimensional (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    FiniteDimensional ℚ (twelfthKummerField q a) := by
  rw [twelfthKummerField_eq_sup]
  infer_instance

instance twelfthKummerField_isGalois (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    IsGalois ℚ (twelfthKummerField q a) := by
  have hn : Normal ℚ (twelfthKummerField q a) := by
    rw [twelfthKummerField_eq_sup]
    infer_instance
  exact {}

instance twelfthKummerField_numberField (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    NumberField (twelfthKummerField q a) where

instance twelfthKummerField_isGalois_over_cyclotomic (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : IsGalois (twelfthCyclotomicField q) (twelfthKummerField q a) :=
  IsGalois.tower_top_of_isGalois ℚ _ _

instance twelfthKummerField_isGalois_over_kummer (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : IsGalois (primeKummerField q a) (twelfthKummerField q a) :=
  IsGalois.tower_top_of_isGalois ℚ _ _

end ArtinMatthews
