module

public import ArtinMatthews.ProbePrimeLocalScalars
public import ArtinMatthews.ProbeSexticGaussPhase
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

/-! The finite sextic phase identities on the actual prime quotient.  The
local correction defined here is not asserted to be a global Hecke value. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField OAI.SevenEighths
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeGaussGamma (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) : ℂ :=
  probePrimeTau K p hp (χ ^ j) / (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)

def probePrimeGaussLocalLambda (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) : ℂ :=
  -(probePrimeGaussGamma K p hp χ 2) ^ 3

def probePrimeGaussLocalG (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) : ℂ :=
  (χ (Ideal.Quotient.mk _ (4 : 𝓞 K)))⁻¹ * probePrimeGaussGamma K p hp χ 3

def probePrimeGaussLocalVartheta (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η : ℂ) : ℂ :=
  star (probePrimeGaussLocalLambda K p hp χ) *
    star (probePrimeGaussLocalG K p hp χ) * η

theorem probePrimeGauss_inverse_pair (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) :
    probePrimeTau K p hp.ne_zero χ * probePrimeTau K p hp.ne_zero (χ ^ 5) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probePrimeTau, tsum_fintype, gaussSum, hc] using
    probeSexticGauss_inverse_pair χ hχ hminus (probePrimePhase K p hp.ne_zero)
      (probePrimePhase_primitive K p hp.ne_zero)

theorem probePrimeGauss_vartheta_phase (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2) (η : ℂ) :
    probePrimeGaussGamma K p hp.ne_zero χ 1 *
      probePrimeGaussGamma K p hp.ne_zero χ 2 *
        probePrimeGaussLocalVartheta K p hp.ne_zero χ η = -η := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hγ (j : ℕ) : probePrimeGaussGamma K p hp.ne_zero χ j =
      probeGaussGamma χ (probePrimePhase K p hp.ne_zero) j := by
    simp only [probePrimeGaussGamma, probePrimeTau, tsum_fintype,
      probeGaussGamma, ProbeGauss.normalizedGauss, gaussSum, hc]
  simp only [probePrimeGaussLocalVartheta, probePrimeGaussLocalLambda,
    probePrimeGaussLocalG, hγ]
  convert probeSexticGauss_vartheta_phase χ hχ (probePrimePhase K p hp.ne_zero)
    (probePrimePhase_primitive K p hp.ne_zero) hchar η using 1
  simp only [probeGaussLocalVartheta, probeGaussLocalLambda, probeGaussLocalG, map_ofNat]

end

end ArtinMatthews.VaryingKummerAnalytic
