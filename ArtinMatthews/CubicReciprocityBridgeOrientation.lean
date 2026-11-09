module

public import ArtinMatthews.CubicThetaFieldComparison
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-!+# Orienting the cyclotomic comparison by the actual Eisenstein embedding

The comparison is constructed by extending the specified embedding on the
ring of integers to its fraction field. Thus it preserves the chosen complex
orientation, rather than choosing an arbitrary cyclotomic isomorphism.
-/

noncomputable section

namespace ArtinMatthews
open OAI OAI.SevenEighths

local notation "EK" => HeckeFamily.K
local notation "EO" => HeckeFamily.O

theorem eisensteinOmega_mem_cubicCyclotomicField :
    EisensteinEmbedding.omega3 ∈ cubicCyclotomicField := by
  apply cube_unity_mem_cubicCyclotomicField
  have h := EisensteinEmbedding.omega3_sq
  linear_combination (EisensteinEmbedding.omega3 - 1) * h

theorem eisEmbedding_mem_cubicCyclotomicField (a : EO) :
    ConcreteTraceCRT.eisEmbedding a ∈ cubicCyclotomicField := by
  obtain ⟨m, n, rfl⟩ := EisensteinEmbedding.exists_ab a
  change EisensteinEmbedding.embedding EisensteinEmbedding.omega3
    EisensteinEmbedding.omega3_sq _ ∈ cubicCyclotomicField
  rw [EisensteinEmbedding.embedding_apply_ab]
  exact cubicCyclotomicField.add_mem (cubicCyclotomicField.intCast_mem m)
    (cubicCyclotomicField.mul_mem (cubicCyclotomicField.intCast_mem n)
      eisensteinOmega_mem_cubicCyclotomicField)

/-- The specified Eisenstein embedding, with codomain restricted to the
actual cubic cyclotomic subfield of the complex numbers. -/
def orientedEisensteinIntegers : EO →+* cubicCyclotomicField :=
  ConcreteTraceCRT.eisEmbedding.codRestrict cubicCyclotomicField.toSubring
    eisEmbedding_mem_cubicCyclotomicField

theorem orientedEisensteinIntegers_injective : Function.Injective orientedEisensteinIntegers := by
  intro a b h
  apply ConcreteTraceCRT.eisEmbedding_injective
  exact congrArg (fun z : cubicCyclotomicField => (z : ℂ)) h

/-- Extension of the specified embedding to the fraction field. -/
def orientedHeckeCyclotomicHom : EK →ₐ[ℚ] cubicCyclotomicField :=
  (IsFractionRing.lift orientedEisensteinIntegers_injective : EK →+* cubicCyclotomicField).toRatAlgHom

@[simp] theorem orientedHeckeCyclotomicHom_coe_integer (a : EO) :
    (orientedHeckeCyclotomicHom (a : EK) : ℂ) = ConcreteTraceCRT.eisEmbedding a := by
  change ((IsFractionRing.lift orientedEisensteinIntegers_injective : EK →+* cubicCyclotomicField)
    (algebraMap EO EK a) : ℂ) = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

theorem orientedHeckeCyclotomicHom_bijective : Function.Bijective orientedHeckeCyclotomicHom := by
  have : FiniteDimensional ℚ cubicCyclotomicField :=
    FiniteDimensional.of_injective heckeCyclotomicEquiv.symm.toLinearMap
      heckeCyclotomicEquiv.symm.injective
  refine ⟨orientedHeckeCyclotomicHom.injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := orientedHeckeCyclotomicHom.toLinearMap)
    heckeCyclotomicEquiv.toLinearEquiv.finrank_eq).mp orientedHeckeCyclotomicHom.injective

/-- The cyclotomic field comparison oriented by `ConcreteTraceCRT.eisEmbedding`. -/
def orientedHeckeCyclotomicEquiv : EK ≃ₐ[ℚ] cubicCyclotomicField :=
  AlgEquiv.ofBijective orientedHeckeCyclotomicHom orientedHeckeCyclotomicHom_bijective

@[simp] theorem coe_orientedHeckeCyclotomicEquiv_integer (a : EO) :
    (orientedHeckeCyclotomicEquiv (a : EK) : ℂ) = ConcreteTraceCRT.eisEmbedding a :=
  orientedHeckeCyclotomicHom_coe_integer a

/-- The induced oriented isomorphism on the actual rings of integers. -/
def orientedHeckeCyclotomicIntegersEquiv :
    EO ≃+* NumberField.RingOfIntegers cubicCyclotomicField :=
  NumberField.RingOfIntegers.mapRingEquiv orientedHeckeCyclotomicEquiv.toRingEquiv

@[simp] theorem coe_orientedHeckeCyclotomicIntegersEquiv (a : EO) :
    (((orientedHeckeCyclotomicIntegersEquiv a :
      NumberField.RingOfIntegers cubicCyclotomicField) : cubicCyclotomicField) : ℂ) =
        ConcreteTraceCRT.eisEmbedding a := by
  exact coe_orientedHeckeCyclotomicEquiv_integer a

end ArtinMatthews
