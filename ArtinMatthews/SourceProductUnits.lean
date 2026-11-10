module

public import ArtinMatthews.SourceLocalUnits
public import ArtinMatthews.QuotientUnitChanges
public import ArtinMatthews.SourceCRTCofactorPhase
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

/-! Concrete prime-local units and standard phases on the exact product
quotient used by the finite source kernel. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceProductUnit (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ :=
  Units.map (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ P k t)).toMonoidHom
    (sourcePrimePowerUnit S₀ P hP a ha (k + t) x hx)

theorem sourceProductUnit_val (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (sourceProductUnit S₀ P hP a ha k t x hx :
        (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)) =
      Ideal.Quotient.mk _ x := by
  change (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ P k t))
    (sourcePrimePowerUnit S₀ P hP a ha (k + t) x hx :
      (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P (k + t)) = _
  rw [sourcePrimePowerUnit_val]
  exact Ideal.quotEquivOfEq_mk _ x

theorem sourceProductUnit_left (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (quotientUnitProjection (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (sourceProductUnit S₀ P hP a ha k t x hx) :
      (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P k) = Ideal.Quotient.mk _ x := by
  change (Ideal.Quotient.factor (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _))
    (sourceProductUnit S₀ P hP a ha k t x hx :
      (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)) = _
  rw [sourceProductUnit_val]
  rfl

theorem sourceProductUnit_right (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (quotientUnitProjection (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (sourceProductUnit S₀ P hP a ha k t x hx) :
      (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P t) = Ideal.Quotient.mk _ x := by
  change (Ideal.Quotient.factor (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _))
    (sourceProductUnit S₀ P hP a ha k t x hx :
      (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)) = _
  rw [sourceProductUnit_val]
  rfl

def sourceLocalProductPhase (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (k t : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ P k t).symm)
    (sourcePrimePowerPhase S₀ P a ha (k + t))

theorem sourceLocalProductPhase_mk (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (k t : ℕ) (x : PrincipalIntegerRing S₀) :
    sourceLocalProductPhase S₀ P a ha k t (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / (a : K) ^ (k + t)) := by
  rw [sourceLocalProductPhase, pullAddChar_apply, Ideal.quotEquivOfEq_mk, sourcePrimePowerPhase_mk]

end
end ArtinMatthews.SourceCRTNormalization
