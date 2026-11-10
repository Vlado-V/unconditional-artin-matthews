module

public import ArtinMatthews.SIntegerSourceSexticF
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplicativity of the actual source power weights, including the
constant-one absent modulus and all positive-modulus unit masks. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem generatorPowerWeight_mul (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (x y : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) :
    generatorPowerWeight S₀ P hP a ha χ n (x * y) =
      generatorPowerWeight S₀ P hP a ha χ n x * generatorPowerWeight S₀ P hP a ha χ n y := by
  by_cases hn : 0 < n
  · simp only [generatorPowerWeight, dite_eq_left hn, map_mul]
  · simp only [generatorPowerWeight, dite_eq_right hn, one_mul]

theorem generatorPowerWeight_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    generatorPowerWeight S₀ P hP a ha χ n 1 = 1 := by
  by_cases hn : 0 < n
  · simp only [generatorPowerWeight, dite_eq_left hn, map_one]
  · simp only [generatorPowerWeight, dite_eq_right hn]

theorem sourceLocalPowerWeight_mul (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (x y : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) :
    sourceLocalPowerWeight S₀ P hP a ha χ n (x * y) =
      sourceLocalPowerWeight S₀ P hP a ha χ n x * sourceLocalPowerWeight S₀ P hP a ha χ n y := by
  unfold sourceLocalPowerWeight
  erw [map_mul]
  exact generatorPowerWeight_mul S₀ P hP a ha χ n _ _

theorem sourceLocalPowerWeight_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    sourceLocalPowerWeight S₀ P hP a ha χ n 1 = 1 := by
  unfold sourceLocalPowerWeight
  erw [map_one]
  exact generatorPowerWeight_one S₀ P hP a ha χ n

end
end ArtinMatthews.SourceCRTNormalization
