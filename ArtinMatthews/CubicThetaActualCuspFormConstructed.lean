module

public import ArtinMatthews.CubicThetaActualCuspForm
public import ArtinMatthews.CubicThetaConstructedWeil
public import ArtinMatthews.CubicTrace
public import ArtinMatthews.CubicReciprocityBridgeHeckeActual
public import ArtinMatthews.CubicReciprocityNonprincipalCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Native cusp forms for the actual cubic Galois Fourier terms, using the
existing constructed Weil representation and retaining exact ideal coefficients. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups BigOperators
open Complex UpperHalfPlane
open OAI OAI.SevenEighths

/-- The actual cubic numerator theta cusp form, with no representation or
modularity hypothesis. Its underlying function is the defining ideal theta. -/
def actualCubicNumeratorHeckeThetaCuspForm
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) :
    CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1 :=
  cubicNumeratorHeckeThetaCuspForm cubicThetaWeilData A hA hnoncube

@[simp] theorem actualCubicNumeratorHeckeThetaCuspForm_coe
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) :
    (fun τ => actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube τ) =
      heckeTheta (cubicNumeratorHeckeCharacter A hA) := rfl

/-- Exact q-coefficients are preserved by the native cusp-form packaging. -/
theorem actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) (n : ℕ) :
    (qExpansion 1 (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)).coeff n =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  heckeTheta_qExpansion_coeff _ n

theorem actualCubicNumeratorHeckeThetaCuspForm_ne_zero
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) :
    actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube ≠ 0 := by
  intro hz
  have h := congrArg (fun f : CuspForm
    (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1 => (fun τ => f τ)) hz
  exact heckeTheta_ne_zero _ h

/-- Every nonconstant term of the actual Galois Fourier expansion has a
literal native cusp form. The level, original prime support, exact q-coefficients
and good-prime Frobenius traces are retained together. -/
theorem cubicFourier_character_has_actual_cuspForm {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0) :
    ∃ (A : ℤ) (hA : A ≠ 0)
      (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (fun τ => f τ) = heckeTheta (cubicNumeratorHeckeCharacter A hA) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n =
        idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n) ∧
      f ≠ 0 ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        (∀ a ∈ S, ¬ (p : ℤ) ∣ a) →
        (qExpansion 1 f).coeff p =
          cubicTrace (χ (Additive.ofMul (relativeCubicFrobenius D hp3))) := by
  obtain ⟨A, hA, hdiv, _, hnonprincipal, htrace⟩ :=
    cubicFourier_character_has_thetaTrace hzero χ
  have hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein) := by
    intro hy
    exact hnonprincipal hχ ((cubicNumeratorHeckeCharacter_principal_iff A hA).mpr hy)
  refine ⟨A, hA, actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube,
    hdiv, rfl, ?_, actualCubicNumeratorHeckeThetaCuspForm_ne_zero A hA hnoncube, ?_⟩
  · exact actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff A hA hnoncube
  · intro p hp hp3 D hpS
    rw [actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff]
    exact htrace p hp3 D hpS

end ArtinMatthews
