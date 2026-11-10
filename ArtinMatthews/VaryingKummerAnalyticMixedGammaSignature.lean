module

public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMellin
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Explicit real/complex signature normalization for the mixed Gaussian Mellin factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedGammaFactor_signature (s : ℂ) :
    mixedGammaFactor K s =
      ((1/2 : ℂ)*(Real.pi : ℂ)^(-(s/2))*Complex.Gamma (s/2))^
          InfinitePlace.nrRealPlaces K *
      ((1/2 : ℂ)*(Real.pi : ℂ)^(-s)*Complex.Gamma s)^
          InfinitePlace.nrComplexPlaces K := by
  unfold mixedGammaFactor
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  simp only [InfinitePlace.mult_isReal, InfinitePlace.mult_isComplex,
    Nat.cast_one, Nat.cast_ofNat, one_mul,
    show ∀ s : ℂ, 2*s/2 = s by intro s; ring,
    Finset.prod_const, Finset.card_univ]

theorem mixedRadialJacobian_signature :
    mixedRadialJacobian K = (2 / (Module.finrank ℚ K : ℝ)) *
      2^(InfinitePlace.nrComplexPlaces K) := by
  unfold mixedRadialJacobian
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  simp only [InfinitePlace.mult_isReal, InfinitePlace.mult_isComplex,
    Nat.cast_one, Nat.cast_ofNat, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.card_univ]

end
end ArtinMatthews.VaryingKummerAnalytic
