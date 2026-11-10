module

public import ArtinMatthews.CubicReciprocityBridgeOrientation
public import ArtinMatthews.CubicFrobeniusConditionKummer
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
# The Eisenstein base inside the actual integral Kummer extension

The embedding of rings of integers and the fixed-ring property below are
constructed from the concrete Kummer field and its actual fixing subgroup.
-/
noncomputable section
open scoped NumberField

namespace ArtinMatthews
open OAI.SevenEighths.HeckeFamily

/-- The cubic cyclotomic base embedded in the actual Kummer field. -/
def heckeKummerFieldEmbedding (S : Finset ℤ) : K →ₐ[ℚ] integerCubicField S :=
  (IntermediateField.inclusion
    (cubicCyclotomicField_le_cubicKummerField (integerCubicBases S))).comp
      orientedHeckeCyclotomicEquiv.toAlgHom

/-- The induced actual embedding on rings of integers. -/
def heckeKummerIntegersEmbedding (S : Finset ℤ) : O →+* 𝓞 (integerCubicField S) :=
  NumberField.RingOfIntegers.mapRingHom (heckeKummerFieldEmbedding S).toRingHom

instance heckeKummerIntegersAlgebra (S : Finset ℤ) :
    Algebra O (𝓞 (integerCubicField S)) :=
  (heckeKummerIntegersEmbedding S).toAlgebra

@[simp] theorem heckeKummerIntegers_algebraMap (S : Finset ℤ) (a : O) :
    algebraMap O (𝓞 (integerCubicField S)) a = heckeKummerIntegersEmbedding S a := rfl

@[simp] theorem coe_heckeKummerIntegersEmbedding (S : Finset ℤ) (a : O) :
    (heckeKummerIntegersEmbedding S a : integerCubicField S) =
      heckeKummerFieldEmbedding S (a : K) := rfl

/-- The actual integral embedding has exactly the complex orientation used
in the cubic residue symbols. -/
@[simp] theorem coe_heckeKummerIntegersEmbedding_complex (S : Finset ℤ) (a : O) :
    (((heckeKummerIntegersEmbedding S a : 𝓞 (integerCubicField S)) :
      integerCubicField S) : ℂ) = OAI.ConcreteTraceCRT.eisEmbedding a :=
  coe_orientedHeckeCyclotomicEquiv_integer a

theorem integerCubicGalois_fixes_heckeEmbedding (S : Finset ℤ)
    (σ : integerCubicGaloisGroup S) (a : K) :
    σ.val (heckeKummerFieldEmbedding S a) = heckeKummerFieldEmbedding S a := by
  apply (IntermediateField.mem_fixingSubgroup_iff _ σ.val).mp σ.property
  exact (orientedHeckeCyclotomicEquiv a).property

theorem integerCubicGalois_fixes_heckeIntegers (S : Finset ℤ)
    (σ : integerCubicGaloisGroup S) (a : O) :
    σ • (heckeKummerIntegersEmbedding S a) = heckeKummerIntegersEmbedding S a := by
  apply Subtype.ext
  exact integerCubicGalois_fixes_heckeEmbedding S σ a

instance heckeKummerIntegers_smulCommClass (S : Finset ℤ) :
    SMulCommClass (integerCubicGaloisGroup S) O (𝓞 (integerCubicField S)) where
  smul_comm σ a b := by
    change σ • (algebraMap O (𝓞 (integerCubicField S)) a * b) =
      algebraMap O (𝓞 (integerCubicField S)) a * (σ • b)
    rw [smul_mul', heckeKummerIntegers_algebraMap,
      integerCubicGalois_fixes_heckeIntegers]

/-- Fixed algebraic integers in the Kummer field come from actual Eisenstein
integers, rather than from an assumed fixed-ring presentation. -/
instance heckeKummerIntegers_isInvariant (S : Finset ℤ) :
    Algebra.IsInvariant O (𝓞 (integerCubicField S)) (integerCubicGaloisGroup S) where
  isInvariant x hx := by
    have hfixed : (x : integerCubicField S) ∈
        IntermediateField.fixedField (integerCubicGaloisGroup S) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact congrArg (fun y : 𝓞 (integerCubicField S) => (y : integerCubicField S))
        (hx ⟨σ, hσ⟩)
    rw [IsGalois.fixedField_fixingSubgroup] at hfixed
    let b : cubicCyclotomicField := ⟨((x : integerCubicField S) : ℂ), hfixed⟩
    let a : K := orientedHeckeCyclotomicEquiv.symm b
    have ha : heckeKummerFieldEmbedding S a = (x : integerCubicField S) := by
      apply Subtype.ext
      change ((orientedHeckeCyclotomicEquiv (orientedHeckeCyclotomicEquiv.symm b) : cubicCyclotomicField) : ℂ) = _
      rw [AlgEquiv.apply_symm_apply]
    have hai : IsIntegral ℤ a := by
      apply (isIntegral_algHom_iff ((heckeKummerFieldEmbedding S).restrictScalars ℤ)
        (heckeKummerFieldEmbedding S).injective).mp
      change IsIntegral ℤ (heckeKummerFieldEmbedding S a)
      rw [ha]
      exact x.property
    refine ⟨⟨a, hai⟩, ?_⟩
    apply Subtype.ext
    exact ha

instance heckeKummerIntegers_faithfulSMul (S : Finset ℤ) :
    FaithfulSMul O (𝓞 (integerCubicField S)) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro a b hab
  apply NumberField.RingOfIntegers.coe_injective
  apply (heckeKummerFieldEmbedding S).injective
  exact congrArg (fun x : 𝓞 (integerCubicField S) => (x : integerCubicField S)) hab

instance heckeKummerIntegers_isIntegral (S : Finset ℤ) :
    Algebra.IsIntegral O (𝓞 (integerCubicField S)) :=
  Algebra.IsInvariant.isIntegral O (𝓞 (integerCubicField S)) (integerCubicGaloisGroup S)

/-- A prime above a prescribed Eisenstein prime and an actual relative
arithmetic Frobenius lift at that prime. -/
structure EisensteinFrobeniusData (S : Finset ℤ) (P : Ideal O) where
  primeIdeal : Ideal (𝓞 (integerCubicField S))
  maximal : primeIdeal.IsMaximal
  liesOver : primeIdeal.LiesOver P
  frobenius : integerCubicGaloisGroup S
  frobenius_spec : IsArithFrobAt O frobenius primeIdeal

/-- Both the prime and relative Frobenius lift are supplied by the actual
integral invariant-ring extension. -/
theorem exists_eisensteinFrobeniusData (S : Finset ℤ) (P : Ideal O) [P.IsMaximal] :
    Nonempty (EisensteinFrobeniusData S P) := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (integerCubicField S)) P
  let : Q.IsMaximal := hQ
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant O (integerCubicGaloisGroup S) Q
  exact ⟨⟨Q, hQ, hQP, σ, hσ⟩⟩

end ArtinMatthews
