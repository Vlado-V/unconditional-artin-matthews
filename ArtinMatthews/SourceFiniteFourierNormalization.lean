module

public import ArtinMatthews.SIntegerFiniteSourceFourier
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The source q_s^(-1/2) normalization of the genuine finite Fourier
sum.  The resulting multiplier is exactly sqrt(q_s), including unit
moduli, rather than an unspecified positive constant. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceNormalizedPeriodicFourier (s A : PrincipalIntegerRing S₀)
    (hs : s ≠ 0) (hA : A ≠ 0)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) : ℂ :=
  ∑' m : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s * A},
    (sourceResidueGauss S₀ s hs f (-Quotient.out m) /
        (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ)) *
      g (Ideal.Quotient.mk _ (Quotient.out m)) *
      sIntegerQuotientPhase K (principalizingSet S₀) (s * A) (mul_ne_zero hs hA)
        (Ideal.Quotient.mk _ (h * Quotient.out m))

theorem sourceNormalizedPeriodicFourier_eq_div (s A : PrincipalIntegerRing S₀)
    (hs : s ≠ 0) (hA : A ≠ 0)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) :
    sourceNormalizedPeriodicFourier S₀ s A hs hA f g h =
      sourcePeriodicFourier S₀ s A hs hA f g h /
        (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ) := by
  unfold sourceNormalizedPeriodicFourier sourcePeriodicFourier
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

theorem sourceQuotientNorm_pos (s : PrincipalIntegerRing S₀) (hs : s ≠ 0) :
    0 < sourceQuotientNorm S₀ s := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {s}) :=
    principal_element_quotient_finite S₀ s hs
  exact Nat.card_pos

theorem sourceQuotientNorm_div_sqrt (s : PrincipalIntegerRing S₀) (hs : s ≠ 0) :
    (sourceQuotientNorm S₀ s : ℂ) /
      (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ) =
      (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ) := by
  have hpos : (0 : ℝ) < sourceQuotientNorm S₀ s := by
    exact_mod_cast sourceQuotientNorm_pos S₀ s hs
  have hne : (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  apply (div_eq_iff hne).mpr
  exact_mod_cast (Real.mul_self_sqrt (le_of_lt hpos)).symm

theorem sourceNormalizedPeriodicFourier_eq (s A : PrincipalIntegerRing S₀)
    (hs : s ≠ 0) (hA : A ≠ 0)
    (hphase : (sIntegerQuotientPhase K (principalizingSet S₀) (s * A)
      (mul_ne_zero hs hA)).IsPrimitive)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {s} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A} → ℂ) (h : PrincipalIntegerRing S₀) :
    sourceNormalizedPeriodicFourier S₀ s A hs hA f g h =
      (Real.sqrt (sourceQuotientNorm S₀ s) : ℂ) *
        sourceFiniteF S₀ s A h (fun x => f (Ideal.Quotient.mk _ x))
          (fun x => g (Ideal.Quotient.mk _ x)) := by
  rw [sourceNormalizedPeriodicFourier_eq_div,
    sourcePeriodicFourier_eq S₀ s A hs hA hphase, mul_div_right_comm,
    sourceQuotientNorm_div_sqrt S₀ s hs]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourceFamilyNormalizedPeriodicFourier_eq (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (hbad : ∀ i, P i ∉ traceBadPlaces K)
    (f : (PrincipalIntegerRing S₀) ⧸ Ideal.span {∏ i, a i ^ k i} → ℂ)
    (g : (PrincipalIntegerRing S₀) ⧸ Ideal.span {∏ i, a i ^ t i} → ℂ)
    (h : PrincipalIntegerRing S₀) :
    sourceNormalizedPeriodicFourier S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i)
      (generatorProduct_ne_zero S₀ P a ha k) (generatorProduct_ne_zero S₀ P a ha t) f g h =
      (Real.sqrt (sourceQuotientNorm S₀ (∏ i, a i ^ k i)) : ℂ) *
        sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) h
          (fun x => f (Ideal.Quotient.mk _ x)) (fun x => g (Ideal.Quotient.mk _ x)) := by
  rw [sourceNormalizedPeriodicFourier_eq_div,
    sourceFamilyPeriodicFourier_eq S₀ P hP hS a ha k t hbad, mul_div_right_comm,
    sourceQuotientNorm_div_sqrt S₀ _ (generatorProduct_ne_zero S₀ P a ha k)]

end
end ArtinMatthews.SIntegerFourier
