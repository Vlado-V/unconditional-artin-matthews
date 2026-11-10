module

public import ArtinMatthews.SIntegerSourceFiniteF
public import ArtinMatthews.SIntegerSexticTransport
public import ArtinMatthews.SIntegerExteriorGenerator
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
public import Mathlib.RingTheory.Henselian
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

/-! Source-faithful sextic weights and the finite F factorization for
actual exterior S-integer prime generators. Global generators are the
literal products, and local weights keep the absent-modulus convention. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceLocalPowerWeight (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (z : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) : ℂ :=
  generatorPowerWeight S₀ P hP a ha χ n
    (Ideal.quotEquivOfEq (generator_power_ideal S₀ P a ha n) z)

theorem sourceLocalPowerWeight_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (z : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 0) :
    sourceLocalPowerWeight S₀ P hP a ha χ 0 z = 1 := rfl

def sourceSexticWeight (P : ι → HeightOneSpectrum (𝓞 K))
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (n : ι → ℕ)
    (x : PrincipalIntegerRing S₀) : ℂ :=
  crtResidueWeight S₀ P n
    (fun i => sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) (n i)) x

omit [DecidableEq ι] in
theorem generatorProduct_ne_zero (P : ι → HeightOneSpectrum (𝓞 K))
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) : (∏ i, a i ^ n i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero (n i) (exterior_generator_ne_zero S₀ (P i) (a i) (ha i))

theorem sourceSexticFiniteF_factor
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Pairwise fun i j => P i ≠ P j)
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (k t : ι → ℕ) (h : PrincipalIntegerRing S₀) :
    sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) h
      (sourceSexticWeight S₀ P hS a ha χ k) (sourceSexticWeight S₀ P hS a ha χ t) =
      ∏ i, sourceCRTLocalSum S₀ P k t hP
        (sourceCRTPhase S₀ P (fun i => k i + t i)
          ((∏ i, a i ^ k i) * (∏ i, a i ^ t i))
          (mul_ne_zero (generatorProduct_ne_zero S₀ P a ha k) (generatorProduct_ne_zero S₀ P a ha t))
          (sourceCRT_modulus_product S₀ P k t _ _
            (crtModulus_generator S₀ P k a ha) (crtModulus_generator S₀ P t a ha)))
        (∏ i, a i ^ t i) h
        (fun i => sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) (k i))
        (fun i => sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) (t i)) i :=
  sourceFiniteF_factor S₀ P k t hP hS _ _ h
    (generatorProduct_ne_zero S₀ P a ha k) (generatorProduct_ne_zero S₀ P a ha t)
    (crtModulus_generator S₀ P k a ha) (crtModulus_generator S₀ P t a ha) _ _

end
end ArtinMatthews.SIntegerQuotient
