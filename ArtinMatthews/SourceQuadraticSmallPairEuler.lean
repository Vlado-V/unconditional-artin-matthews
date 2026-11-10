module

public import ArtinMatthews.SourceQuadraticSmallEuler
public import ArtinMatthews.SourceQuadraticBlockSmallContour
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.SourceQuadraticPairConductor
public import ArtinMatthews.SourceQuadraticSmallResidue
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

/-- The full divisor factor in Small separates on an actual same-class pair. -/
theorem sourceQuadraticSmallPairEuler (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (s : ℂ) :
    quadraticSmallEuler F (sourceQuadraticBlockSquareModulus F S₀ hζ g ((b - g) + (c - g))) s =
      quadraticSmallEuler F (sourceQuadraticBlockModulus F S₀ g) s *
        quadraticSmallEuler F (I (b - g)) s * quadraticSmallEuler F (I (c - g)) s := by
  have hdata := sourceQuadraticPair_residual_data F S₀ b c g hb hc hg
  have hcop := (sourceQuadraticBlock_ideal_coprime_iff F S₀ (b - g) (c - g)).mpr hdata.2.2.1
  rw [sourceQuadraticBlockSquareModulus,
    sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass,
    quadraticSmallEuler_mul F (sourceQuadraticBlockModulus_ne_bot F S₀ g)
      (mul_ne_zero (sourcePrimeExponentIdeal_ne_bot F S₀ (b - g))
        (sourcePrimeExponentIdeal_ne_bot F S₀ (c - g)))
      (sourceQuadratic_commonModulus_coprime_residualProduct F S₀ b c g hb hc),
    quadraticSmallEuler_mul F (sourcePrimeExponentIdeal_ne_bot F S₀ (b - g))
      (sourcePrimeExponentIdeal_ne_bot F S₀ (c - g)) hcop]
  ring

end
end ArtinMatthews.SourceEulerAssembly
