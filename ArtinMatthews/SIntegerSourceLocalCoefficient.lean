module

public import ArtinMatthews.SIntegerLocalHigher
public import ArtinMatthews.SIntegerLocalAbsent
public import ArtinMatthews.SIntegerLocalCOneValues
public import ArtinMatthews.SIntegerLocalCZeroValues
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

/-! The full local source coefficient, presented by the two actual
modulus degrees. Absent moduli have their single trivial residue;
positive moduli retain the unit mask even at a sixth-power exponent. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def standardLocalCoefficient (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) : ℕ → ℕ → ℕ → ℂ
  | 0, 0, _ => 1
  | 0, k + 1, J => standardLocalAbsent S₀ P hP a ha χ k J
  | t + 1, 0, J => standardLocalCZero S₀ P hP a ha χ t J
  | t + 1, 1, J => standardLocalCOne S₀ P hP a ha χ t J
  | t + 1, k + 2, J => standardLocalHigher S₀ P hP a ha χ (k + 1) t J

theorem standardLocalCoefficient_zero_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (J : ℕ) :
    standardLocalCoefficient S₀ P hP a ha χ 0 0 J = 1 := rfl

theorem standardLocalCoefficient_zero_succ (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) :
    standardLocalCoefficient S₀ P hP a ha χ 0 (k + 1) J = if J = 0 then 1 else 0 :=
  standardLocalAbsent_eq S₀ P hP a ha χ k J

theorem standardLocalCoefficient_succ_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (t J : ℕ) :
    standardLocalCoefficient S₀ P hP a ha χ (t + 1) 0 J =
      if t ≤ J then (Ideal.absNorm P.asIdeal : ℂ) ^ t *
        (if t = J then residueSourceTau S₀ P hP a ha (χ ^ (t + 1))
          else if 6 ∣ t + 1 then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else 0 := standardLocalCZero_eq S₀ P hP a ha hbad χ hχ t J

theorem standardLocalCoefficient_succ_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (hminus : χ (-1) = 1) (t J : ℕ) :
    standardLocalCoefficient S₀ P hP a ha χ (t + 1) 1 J =
      if t + 1 ≤ J then residueSourceTau S₀ P hP a ha χ *
        (Ideal.absNorm P.asIdeal : ℂ) ^ t *
        (if t + 1 = J then residueSourceTau S₀ P hP a ha (χ ^ t)
          else if 6 ∣ t then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else 0 := standardLocalCOne_eq S₀ P hP a ha hbad χ hχ hminus t J

theorem standardLocalCoefficient_succ_add_two (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t k J : ℕ) :
    standardLocalCoefficient S₀ P hP a ha χ (t + 1) (k + 2) J = 0 :=
  standardLocalHigher_eq_zero S₀ P hP a ha hbad χ (k + 1) t J (Nat.succ_pos _)

end
end ArtinMatthews.SIntegerFourier
