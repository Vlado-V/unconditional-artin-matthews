module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import OAI.NumberTheory.DirichletL.ConductorPresentation


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine primitive conductor descent for residue characters of arbitrary
number fields. The full original-unit mask records the omitted prime factors. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The existing finite-ring conductor construction is instantiated with the
actual ring of integers and its genuinely finite ideal quotient. -/
theorem exists_primitive_residue_conductor
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ) :
    ∃ (f : Ideal (𝓞 K)) (φ : MulChar ((𝓞 K) ⧸ f) ℂ) (hMf : M ≤ f),
      f ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ f.absNorm ≤ M.absNorm ∧
      (∀ a : 𝓞 K, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk f a) else 0) ∧
      φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMf).toMonoidHom) = χ.toUnitHom ∧
      ∀ a : 𝓞 K, IsCoprime (Ideal.span {a}) M →
        χ (Ideal.Quotient.mk M a) = φ (Ideal.Quotient.mk f a) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  obtain ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask⟩ :=
    OAI.SevenEighths.ConductorPresentation.exists_primitive_presentation M χ
  refine ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask, ?_, ?_⟩
  · exact OAI.SevenEighths.ConductorPresentation.unit_factorization_of_mask M f hMf χ φ hmask
  · intro a ha
    simpa only [(quotient_isUnit_iff_span_coprime M a).mpr ha, ite_true] using hmask a

/-- A residue character trivial on global units descends to a genuinely
primitive character with the same global-unit compatibility. -/
theorem exists_primitive_residue_conductor_trivial_on_units
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ u : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (u : 𝓞 K)) = 1) :
    ∃ (f : Ideal (𝓞 K)) (φ : MulChar ((𝓞 K) ⧸ f) ℂ) (hMf : M ≤ f),
      f ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ f.absNorm ≤ M.absNorm ∧
      (∀ a : 𝓞 K, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk f a) else 0) ∧
      φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMf).toMonoidHom) = χ.toUnitHom ∧
      ∀ u : (𝓞 K)ˣ, φ (Ideal.Quotient.mk f (u : 𝓞 K)) = 1 := by
  obtain ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask, hfactor, _⟩ :=
    exists_primitive_residue_conductor M hM χ
  refine ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask, hfactor, ?_⟩
  intro u
  have hu : IsUnit (Ideal.Quotient.mk M (u : 𝓞 K)) := u.isUnit.map (Ideal.Quotient.mk M)
  have he := hmask (u : 𝓞 K)
  rw [hunit u, ite_eq_left hu] at he
  exact he.symm

end
end ArtinMatthews.VaryingKummerAnalytic
