module

public import ArtinMatthews.ProbeIdealPrimeGauss
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

open NumberField IsDedekindDomain OAI.SevenEighths
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealGaussGamma (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) : ℂ :=
  probeIdealTau K P (χ ^ j) / (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)

def probeIdealGaussLocalLambda (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) : ℂ :=
  -(probeIdealGaussGamma K P χ 2) ^ 3

def probeIdealGaussLocalG (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) : ℂ :=
  (χ (Ideal.Quotient.mk _ (4 : 𝓞 K)))⁻¹ * probeIdealGaussGamma K P χ 3

def probeIdealGaussLocalVartheta (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η : ℂ) : ℂ :=
  star (probeIdealGaussLocalLambda K P χ) *
    star (probeIdealGaussLocalG K P χ) * η

theorem probeIdealGauss_inverse_pair (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) :
    probeIdealTau K P χ * probeIdealTau K P (χ ^ 5) =
      (Ideal.absNorm (P.asIdeal) : ℂ) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm (P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probeIdealTau, tsum_fintype, gaussSum, hc] using
    probeSexticGauss_inverse_pair χ hχ hminus (probeIdealResiduePhase K P)
      (probeIdealResiduePhase_primitive K P)

theorem probeIdealGauss_vartheta_phase (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2) (η : ℂ) :
    probeIdealGaussGamma K P χ 1 *
      probeIdealGaussGamma K P χ 2 *
        probeIdealGaussLocalVartheta K P χ η = -η := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm (P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hγ (j : ℕ) : probeIdealGaussGamma K P χ j =
      probeGaussGamma χ (probeIdealResiduePhase K P) j := by
    simp only [probeIdealGaussGamma, probeIdealTau, tsum_fintype,
      probeGaussGamma, ProbeGauss.normalizedGauss, gaussSum, hc]
  simp only [probeIdealGaussLocalVartheta, probeIdealGaussLocalLambda,
    probeIdealGaussLocalG, hγ]
  convert probeSexticGauss_vartheta_phase χ hχ (probeIdealResiduePhase K P)
    (probeIdealResiduePhase_primitive K P) hchar η using 1
  simp only [probeGaussLocalVartheta, probeGaussLocalLambda, probeGaussLocalG, map_ofNat]

end

end ArtinMatthews.VaryingKummerAnalytic
