module

public import ArtinMatthews.KummerTwistedPrimitiveData
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerContinuation
public import ArtinMatthews.IdealRayCharacterProduct
public import ArtinMatthews.SixthKummerSharpRay
public import ArtinMatthews.IdealRayCharacterProductCoefficients
public import ArtinMatthews.IdealRayPrimitivePresentation
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The old-modulus coefficients and continuation of the literal twist.
The Euler-deleted primitive continuation agrees with the Dirichlet series
of `η(I) conjugate(χ_u(I))`, including every original bad-prime mask. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]
variable {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
variable (N : ℕ) (i : ExteriorIdealRowIndex S N)

def twistedKummerOldCharacter : EvenIdealRayCharacter K (twistedKummerOldModulus M S N i) :=
  η.twistInverseAtProduct
    (sixthKummerSharpRayCharacter hζ S hWild (exteriorBoundedIdealRowUnit S N i))
    hM (sixthKummerSharpIdeal_ne_zero S _)

theorem twistedKummerOldCharacter_allCoefficient (I : Ideal (𝓞 K)) :
    (twistedKummerOldCharacter η hM hζ S hWild N i).allCoefficient I =
      η.allCoefficient I * starRingEnd ℂ
        ((sixthKummerSharpRayCharacter hζ S hWild (exteriorBoundedIdealRowUnit S N i)).allCoefficient I) :=
  η.twistInverseAtProduct_allCoefficient _ hM (sixthKummerSharpIdeal_ne_zero S _) I

theorem boundedKummerTwistedPrimitiveDatum_mask
    (d : BoundedKummerTwistedPrimitiveDatum η hM hζ S N i) (I : Ideal (𝓞 K)) :
    (twistedKummerOldCharacter η hM hζ S hWild N i).allCoefficient I =
      if IsCoprime I (twistedKummerOldModulus M S N i) then d.character.allCoefficient I else 0 := by
  apply (twistedKummerOldCharacter η hM hζ S hWild N i).primitiveIdeal_allCoefficient_mask
    (twistedKummerOldModulus_ne_zero hM S N i) d.modulus.val d.old_le d.character
  intro J
  exact d.agrees J

theorem boundedKummerTwistedPrimitiveDatum_coprimeContinued_eq_twisted_dirichlet
    (d : BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)
    (hnp : d.character.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    d.character.idealCoprimeContinued d.modulus.property d.primitive
      (twistedKummerOldModulus M S N i) s =
      ∑' I : Ideal (𝓞 K),
        (twistedKummerOldCharacter η hM hζ S hWild N i).allCoefficient I *
          (Ideal.absNorm I : ℂ)^(-s) := by
  rw [d.character.idealCoprimeContinued_eq_dirichlet d.modulus.property d.primitive hnp
    (twistedKummerOldModulus M S N i) (twistedKummerOldModulus_ne_zero hM S N i) hs]
  apply tsum_congr
  intro I
  rw [boundedKummerTwistedPrimitiveDatum_mask η hM hζ S hWild N i d I]
  split_ifs <;> simp only [zero_mul]

end
end ArtinMatthews
