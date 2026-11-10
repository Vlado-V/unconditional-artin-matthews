module

public import ArtinMatthews.SourceUnitWeightValues
public import ArtinMatthews.SourceProductUnits
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

/-! The two actual source weights as homomorphisms on the common
product-quotient unit group. Their values on local elements are proved. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceProductWeightLeft (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ →* ℂˣ :=
  (Units.map (sourcePowerWeightHom S₀ P hP a ha χ k)).comp
    (Units.map (Ideal.Quotient.factor
      (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)).toMonoidHom)

def sourceProductWeightRight (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ →* ℂˣ :=
  (Units.map (sourcePowerWeightHom S₀ P hP a ha χ t)).comp
    (Units.map (Ideal.Quotient.factor
      (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)).toMonoidHom)

theorem sourceProductWeightLeft_val (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ)
    (u : ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
    (sourceProductWeightLeft S₀ P hP a ha χ k t u : ℂ) =
      sourceLocalPowerWeight S₀ P hP a ha χ k
        (quotientUnitProjection (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _) u) := rfl

theorem sourceProductWeightRight_val (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ)
    (u : ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
    (sourceProductWeightRight S₀ P hP a ha χ k t u : ℂ) =
      sourceLocalPowerWeight S₀ P hP a ha χ t
        (quotientUnitProjection (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _) u) := rfl

theorem sourceProductWeightLeft_element (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceProductWeightLeft S₀ P hP a ha χ k t (sourceProductUnit S₀ P hP a ha k t x hx) =
      sourceCharacterUnit S₀ P hP a ha χ x hx ^ k := by
  apply Units.ext
  rw [sourceProductWeightLeft_val, sourceProductUnit_left, sourcePowerWeight_unitValue,
    Units.val_pow_eq_pow_val]

theorem sourceProductWeightRight_element (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceProductWeightRight S₀ P hP a ha χ k t (sourceProductUnit S₀ P hP a ha k t x hx) =
      sourceCharacterUnit S₀ P hP a ha χ x hx ^ t := by
  apply Units.ext
  rw [sourceProductWeightRight_val, sourceProductUnit_right, sourcePowerWeight_unitValue,
    Units.val_pow_eq_pow_val]

end
end ArtinMatthews.SourceCRTNormalization
