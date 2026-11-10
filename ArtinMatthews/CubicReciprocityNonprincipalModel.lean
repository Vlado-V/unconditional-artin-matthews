module

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
public import ArtinMatthews.CubicFrobeniusConditionKummer
public import OAI.NumberTheory.CubicGram.Definitions
public import OAI.NumberTheory.DirichletL.Hecke.Family
public import ArtinMatthews.CubicReciprocityNonprincipalAlgebra
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
public import OAI.NumberTheory.CubicGram.Coordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete Eisenstein ring comparison needed by cubic numerator characters. -/

namespace ArtinMatthews

open OAI

lemma cubicMoment_omega_eq_hecke_omega :
    CubicFirstMoment.omega = EisensteinEmbedding.omega3 := by
  rw [CubicFirstMoment.omega_eq]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma hecke_coordinateSubring_eq_cubicMoment :
    ConcreteTraceCRT.coordinateSubring = CubicFirstMoment.eisensteinRing.toSubring := by
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨a, b, hz⟩
    change z ∈ CubicFirstMoment.eisensteinRing
    rw [hz, ← cubicMoment_omega_eq_hecke_omega]
    apply CubicFirstMoment.eisensteinRing.add_mem
    · exact CubicFirstMoment.eisensteinRing.algebraMap_mem a
    · exact CubicFirstMoment.eisensteinRing.mul_mem
        (CubicFirstMoment.eisensteinRing.algebraMap_mem b)
        (Algebra.subset_adjoin (Set.mem_singleton _))
  · intro hz
    obtain ⟨a, b, hab⟩ := CubicFirstMoment.exists_coordinates
      (⟨z, hz⟩ : CubicFirstMoment.Eisenstein)
    exact ⟨a, b, by simpa only [cubicMoment_omega_eq_hecke_omega] using hab⟩

/-- A concrete ring isomorphism preserving the chosen complex embedding. -/
noncomputable def heckeIntegersEquivCubicEisenstein :
    OAI.SevenEighths.HeckeFamily.O ≃+* CubicFirstMoment.Eisenstein :=
  ConcreteTraceCRT.ringOfIntegersEquivCoordinateSubring.trans
    (RingEquiv.subringCongr hecke_coordinateSubring_eq_cubicMoment)

@[simp] theorem heckeIntegersEquivCubicEisenstein_coe
    (x : OAI.SevenEighths.HeckeFamily.O) :
    (heckeIntegersEquivCubicEisenstein x : ℂ) = ConcreteTraceCRT.eisEmbedding x := rfl

/-- Nontriviality of the original Kummer Fourier character gives the exact
noncube hypothesis for the complete cubic numerator-character theorem. -/
theorem cubicFourier_radical_not_cube_in_cubicMoment {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) :
    ¬ ∃ y : CubicFirstMoment.Eisenstein, y ^ 3 = (A : CubicFirstMoment.Eisenstein) := by
  rintro ⟨y, hy⟩
  apply cubicFourier_radical_not_cube_in_heckeIntegers χ hχ hR0 hR hrep
  refine ⟨heckeIntegersEquivCubicEisenstein.symm y, ?_⟩
  rw [← map_pow, hy, map_intCast]

end ArtinMatthews
