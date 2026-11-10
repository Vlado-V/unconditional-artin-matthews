module

public import ArtinMatthews.SIntegerSourceLocalCoefficient
public import ArtinMatthews.SourceProductUnits
public import ArtinMatthews.SourceKernelTableBridge
public import ArtinMatthews.SourceLocalUnitChange
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

/-! Actual source unit changes land on the proved literal C coefficient.
All multiplier factors are kept as evaluations of the genuine source
weights on explicitly constructed quotient units. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceLocalUnitFactor (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) : ℂ :=
  let s := sourceProductUnit S₀ P hP a ha k t sp hsp
  let b := sourceProductUnit S₀ P hP a ha k t ap hap
  let c := sourceProductUnit S₀ P hP a ha k t hp hhp
  sourceLocalPowerWeight S₀ P hP a ha χ k
      (quotientUnitProjection (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (c * b⁻¹)) *
    sourceLocalPowerWeight S₀ P hP a ha χ t
      (quotientUnitProjection (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (s * b * c⁻¹))

theorem sourceLocalKernel_eq_coefficient (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t J : ℕ) (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    let s := sourceProductUnit S₀ P hP a ha k t sp hsp
    let b := sourceProductUnit S₀ P hP a ha k t ap hap
    let φ := sourceLocalProductPhase S₀ P a ha k t
    quotientCongruenceKernel (primePowerIdeal S₀ P k) (primePowerIdeal S₀ P t)
        (a ^ t * ap) (a ^ J * hp)
        (φ.mulShift (((s * b)⁻¹ :
          ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
            (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)))
        (sourceLocalPowerWeight S₀ P hP a ha χ k) (sourceLocalPowerWeight S₀ P hP a ha χ t) =
      sourceLocalUnitFactor S₀ P hP a ha χ k t sp ap hp hsp hap hhp *
        standardLocalCoefficient S₀ P hP a ha χ t k J := by
  have h := sourceLocalKernel_unit_change S₀ P hP a ha χ k t J sp ap hp hsp hap hhp
  dsimp only at h
  rw [normalizedKernel_eq_coefficient S₀ P hP a ha χ k t J] at h
  exact h

end
end ArtinMatthews.SourceCRTNormalization
