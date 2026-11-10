module

public import ArtinMatthews.SourcePrimeExponentWeights
public import ArtinMatthews.SourceFiniteSumNorm
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourcePrimeIdealFactorization
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

/-! The actual quotient norms and elementary bound for F(s,A,h),
using the same fixed allowed prime-generator products as the source. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentGenerator_quotient_card (e : SourcePrimeExponents F S₀) :
    Nat.card ((sourceRing F S₀) ⧸ Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e}) =
      sourcePrimeExponentNorm F S₀ e := by
  calc
    _ = Nat.card ((sourceRing F S₀) ⧸
        (sourcePrimeExponentIdeal F S₀ e).map (algebraMap (𝓞 F) (sourceRing F S₀))) :=
      Nat.card_congr (Ideal.quotEquivOfEq
        (sourcePrimeExponentGenerator_ideal F hζ S₀ e).symm).toEquiv
    _ = Ideal.absNorm (sourcePrimeExponentIdeal F S₀ e) :=
      principal_quotient_card (sourceHilbertSeed F S₀) _
        (sourcePrimeExponentIdeal_exterior F S₀ e).2
    _ = sourcePrimeExponentNorm F S₀ e := sourcePrimeExponentIdeal_norm F S₀ e

theorem sourcePrimeExponentGenerator_quotient_finite (e : SourcePrimeExponents F S₀) :
    Finite ((sourceRing F S₀) ⧸ Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e}) := by
  apply Nat.finite_of_card_ne_zero
  rw [sourcePrimeExponentGenerator_quotient_card, ← sourcePrimeExponentIdeal_norm]
  exact Ideal.absNorm_eq_zero_iff.not.mpr (sourcePrimeExponentIdeal_ne_bot F S₀ e)

def sourceExponentFiniteF
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (s A : SourcePrimeExponents F S₀) (h : sourceRing F S₀) : ℂ :=
  sourceFiniteF (sourceHilbertSeed F S₀)
    (sourcePrimeExponentGenerator F hζ S₀ s) (sourcePrimeExponentGenerator F hζ S₀ A) h
    (sourcePrimeExponentWeight F hζ S₀ χ s) (sourcePrimeExponentWeight F hζ S₀ χ A)

theorem sourceExponentFiniteF_norm_le
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (s A : SourcePrimeExponents F S₀) (h : sourceRing F S₀) :
    ‖sourceExponentFiniteF F hζ S₀ χ s A h‖ ≤
      (sourcePrimeExponentNorm F S₀ s : ℝ) * (sourcePrimeExponentNorm F S₀ A : ℝ) := by
  have he := @sourceFiniteSum_norm_le F _ _ (sourceHilbertSeed F S₀)
    (Ideal.span {sourcePrimeExponentGenerator F hζ S₀ s})
    (Ideal.span {sourcePrimeExponentGenerator F hζ S₀ A})
    (sourcePrimeExponentGenerator_quotient_finite F hζ S₀ s)
    (sourcePrimeExponentGenerator_quotient_finite F hζ S₀ A)
    (sourcePrimeExponentGenerator F hζ S₀ s) (sourcePrimeExponentGenerator F hζ S₀ A) h
    (sourcePrimeExponentWeight F hζ S₀ χ s) (sourcePrimeExponentWeight F hζ S₀ χ A)
    (sourcePrimeExponentWeight_norm_le_one F hζ S₀ χ s)
    (sourcePrimeExponentWeight_norm_le_one F hζ S₀ χ A)
  have hs : Nat.card ((PrincipalIntegerRing (sourceHilbertSeed F S₀)) ⧸
      Ideal.span {sourcePrimeExponentGenerator F hζ S₀ s}) = sourcePrimeExponentNorm F S₀ s :=
    sourcePrimeExponentGenerator_quotient_card F hζ S₀ s
  have hA : Nat.card ((PrincipalIntegerRing (sourceHilbertSeed F S₀)) ⧸
      Ideal.span {sourcePrimeExponentGenerator F hζ S₀ A}) = sourcePrimeExponentNorm F S₀ A :=
    sourcePrimeExponentGenerator_quotient_card F hζ S₀ A
  exact he.trans_eq (congrArg₂ (fun m n : ℕ => (m : ℝ) * (n : ℝ)) hs hA)

end
end ArtinMatthews
