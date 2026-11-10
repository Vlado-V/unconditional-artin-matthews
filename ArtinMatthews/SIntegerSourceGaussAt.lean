module

public import ArtinMatthews.SIntegerLocalCZero
public import ArtinMatthews.SIntegerResidueTransform
public import ArtinMatthews.SIntegerFiniteQuotients
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

/-! Fourier sums at arbitrary frequencies in the literal standard
S-integer source phase. No chosen coherent trace phase is substituted. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceGaussAt (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) : ℂ :=
  principalFourier a (a ^ n) (linearPowerPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) n)
    (generatorResidueCharacter S₀ P hP a ha ξ) h

theorem sourceGaussAt_congr (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h h' : PrincipalIntegerRing S₀)
    (hh : h - h' ∈ Ideal.span {a * a ^ n}) :
    sourceGaussAt S₀ P hP a ha ξ n h = sourceGaussAt S₀ P hP a ha ξ n h' := by
  have he : Ideal.Quotient.mk (Ideal.span {a * a ^ n}) h = Ideal.Quotient.mk _ h' :=
    Ideal.Quotient.eq.mpr hh
  unfold sourceGaussAt principalFourier
  simp only [he]

theorem sourceGaussAt_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (n : ℕ) (h : PrincipalIntegerRing S₀) (hh : ¬ a ^ n ∣ h) :
    sourceGaussAt S₀ P hP a ha ξ n h = 0 :=
  principalFourier_zero_off_support a (a ^ n) (exterior_generator_ne_zero S₀ P a ha) _
    (linearPowerPhase_primitive S₀ P hP a ha n hbad) _ h hh

theorem sourceGaussAt_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) :
    sourceGaussAt S₀ P hP a ha ξ n (a ^ n * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ n * residueTransformOnSource S₀ P hP a ha ξ 1 h := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
    principal_element_quotient_finite S₀ a (exterior_generator_ne_zero S₀ P a ha)
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)))
  unfold sourceGaussAt
  rw [principalFourier_lift, linearPowerPhase_lower,
    linearReduction_kernel_card S₀ P hP a ha n, Nat.cast_pow]
  simp only [residueTransformOnSource, pow_one]

end
end ArtinMatthews.SIntegerFourier
