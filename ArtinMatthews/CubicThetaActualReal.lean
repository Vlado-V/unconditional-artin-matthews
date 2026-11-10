module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalConjugationModel
public import ArtinMatthews.CubicReciprocityNonprincipalConjugation
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
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

/-! Reality of the actual cubic theta coefficients, at every natural index.
The proof conjugates the finite ideal norm fiber, including conductor ideals.
-/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths

local notation "EO" => HeckeFamily.O

private instance : IsPrincipalIdealRing EO :=
  IsCyclotomicExtension.Rat.three_pid HeckeFamily.K

/-- Elementwise anti-conjugation descends to the actual ideal character. -/
theorem cubicNumeratorThetaIdeal_conjugate (A : ℤ) (hA : A ≠ 0) (I : Ideal EO) :
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      (I.map heckeIntegerConjugation.toRingHom) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) I) := by
  by_cases hI : I = ⊥
  · subst I
    rw [Ideal.map_bot]
    change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) 0 =
      star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) 0)
    have hz := thetaIdealCharacter_zero (cubicNumeratorHeckeCharacter A hA)
    exact hz.trans ((congrArg star hz).trans (star_zero ℂ)).symm
  let z : EO := Submodule.IsPrincipal.generator I
  have hz : z ≠ 0 := by
    intro h
    apply hI
    rw [← Ideal.span_singleton_generator I]
    change Ideal.span {z} = ⊥
    simp [h]
  have hcz : heckeIntegerConjugation z ≠ 0 :=
    fun h => hz (heckeIntegerConjugation.injective (h.trans (map_zero _).symm))
  rw [← Ideal.span_singleton_generator I]
  change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      ((Ideal.span {z}).map heckeIntegerConjugation.toRingHom) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {z}))
  rw [Ideal.map_span, Set.image_singleton]
  change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      (Ideal.span {heckeIntegerConjugation z}) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {z}))
  rw [thetaIdealCharacter_span _ hcz, thetaIdealCharacter_span _ hz]
  exact cubicNumeratorHeckeCharacter_element_conjugate A hA z

/-- Every actual coefficient is fixed by complex conjugation; no exclusion
of ramified primes or non-coprime indices is necessary. -/
theorem cubicNumeratorThetaCoeff_conjugate (A : ℤ) (hA : A ≠ 0) (n : ℕ) :
    star (idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n) =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  idealThetaCoeff_conj_of_ideal_conjugation _ heckeIntegerConjugation
    (cubicNumeratorThetaIdeal_conjugate A hA) n

/-- The real-part sequence is exactly the complex ideal-sum sequence. -/
theorem cubicNumeratorThetaCoeff_real (A : ℤ) (hA : A ≠ 0) (n : ℕ) :
    ((idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n).re : ℂ) =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  idealThetaCoeff_re_of_ideal_conjugation _ heckeIntegerConjugation
    (cubicNumeratorThetaIdeal_conjugate A hA) n

end ArtinMatthews
