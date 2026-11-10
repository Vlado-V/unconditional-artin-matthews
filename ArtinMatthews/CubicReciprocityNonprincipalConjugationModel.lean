module

public import ArtinMatthews.CubicReciprocityNonprincipalConductor
public import ArtinMatthews.CubicReciprocityNonprincipalModel
public import OAI.NumberTheory.CubicGram.Conjugation
public import OAI.NumberTheory.CubicGram.PrimaryNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Complex conjugation in the concrete integer and residue-ring models. -/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths OAI.CubicFirstMoment

local notation "EO" => HeckeFamily.O

/-- Complex conjugation transported through the embedding-preserving
identification of the two Eisenstein integer models. -/
def heckeIntegerConjugation : EO ≃+* EO :=
  heckeIntegersEquivCubicEisenstein.trans
    (conjugate.trans heckeIntegersEquivCubicEisenstein.symm)

@[simp] theorem heckeIntegerConjugation_model (x : EO) :
    heckeIntegersEquivCubicEisenstein (heckeIntegerConjugation x) =
      conjugate (heckeIntegersEquivCubicEisenstein x) := by
  simp [heckeIntegerConjugation]

@[simp] theorem heckeIntegerConjugation_embedding (x : EO) :
    ConcreteTraceCRT.eisEmbedding (heckeIntegerConjugation x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  rw [← heckeIntegersEquivCubicEisenstein_coe, heckeIntegerConjugation_model,
    conjugate_coe, heckeIntegersEquivCubicEisenstein_coe]

@[simp] theorem heckeIntegerConjugation_involutive (x : EO) :
    heckeIntegerConjugation (heckeIntegerConjugation x) = x := by
  apply heckeIntegersEquivCubicEisenstein.injective
  simp only [heckeIntegerConjugation_model, conjugate_conjugate]

/-- Since `9A` is rational, conjugation acts on its actual residue ring. -/
def cubicNumeratorResidueConjugation (A : ℤ) :
    EO ⧸ cubicNumeratorHeckeModulus A ≃+* EO ⧸ cubicNumeratorHeckeModulus A :=
  Ideal.quotientEquiv _ _ heckeIntegerConjugation (by
    simp only [cubicNumeratorHeckeModulus, Ideal.map_span, Set.image_singleton,
      map_mul, map_intCast, map_ofNat])

@[simp] theorem cubicNumeratorResidueConjugation_mk (A : ℤ) (x : EO) :
    cubicNumeratorResidueConjugation A
      (Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) x) =
      Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) (heckeIntegerConjugation x) := rfl

@[simp] theorem cubicNumeratorResidueConjugation_involutive (A : ℤ)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    cubicNumeratorResidueConjugation A (cubicNumeratorResidueConjugation A x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [cubicNumeratorResidueConjugation_mk, heckeIntegerConjugation_involutive]

/-- Uniqueness of primary associates makes normalization commute with
complex conjugation, including elements divisible by three. -/
theorem primaryNormalize_conjugate (x : Eisenstein) :
    primaryNormalize (conjugate x) = conjugate (primaryNormalize x) := by
  have hunit : IsUnit (Ideal.Quotient.mk (modulus 3) (conjugate x)) ↔
      IsUnit (Ideal.Quotient.mk (modulus 3) x) := by
    have h3 : conjugate (3 : Eisenstein) = 3 := map_ofNat conjugate 3
    have h := isUnit_residue_conjugate (p := (3 : Eisenstein)) (v := x)
    rw [h3] at h
    exact h
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · apply primary_associated_eq (primaryNormalize_primary (hunit.mpr hx))
      (primary_conjugate (primaryNormalize_primary hx))
    apply (primaryNormalize_associated (conjugate x)).symm.trans
    obtain ⟨u, hu⟩ := primaryNormalize_associated x
    refine ⟨Units.map conjugate.toMonoidHom u, ?_⟩
    change conjugate x * conjugate (u : Eisenstein) = _
    simpa only [map_mul] using congrArg conjugate hu
  · simp only [primaryNormalize, dite_eq_right hx, dite_eq_right (mt hunit.mp hx)]

end ArtinMatthews
