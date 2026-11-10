module

public import ArtinMatthews.ProbeLocalSurvivorIndex
public import ArtinMatthews.ProbePrimeGaussPhase
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

/-! The original local index and weights before the j=0 support is grouped.
Here a=Q^(-xi), b=Q^(-w), and V=Q^(-6z). -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeRawTerm (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex) : ℂ :=
  let e : ℕ := if i.1 then 1 else 0
  let t := probeLocalIndexDegree i
  let q : ℂ := Ideal.absNorm (Ideal.span {p})
  let σ : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {p}))
  let γ := probePrimeGaussGamma K p hp χ 2
  let v := probePrimeGaussLocalVartheta K p hp χ η
  γ ^ e * v ^ t * (θ⁻¹) ^ t * (σ⁻¹) ^ e * (q⁻¹) ^ i.2.1 * a ^ t *
    (θ * b) ^ i.2.2.1 * V ^ i.2.2.2 *
      probePrimeLocalCoefficient K p hp χ t i.2.2.1 (6 * i.2.2.2)

def probePrimeRawLocalSeries (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ) : ℂ :=
  ∑' i : ProbeLocalRawIndex, probePrimeRawTerm K p hp χ η θ a b V i

theorem probePrimeRawTerm_zero_of_coefficient (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex)
    (hc : probePrimeLocalCoefficient K p hp χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0) :
    probePrimeRawTerm K p hp χ η θ a b V i = 0 := by
  simp only [probePrimeRawTerm, hc, mul_zero]

theorem probePrimeRawLocalSeries_reindex (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (η θ a b V : ℂ) :
    probePrimeRawLocalSeries K p hp.ne_zero χ η θ a b V =
      ∑' j : ProbeLocalSurvivor,
        probePrimeRawTerm K p hp.ne_zero χ η θ a b V (probeLocalSurvivorIndex j) := by
  apply probeLocal_supported_tsum K p hp χ hχ hminus
  exact probePrimeRawTerm_zero_of_coefficient K p hp.ne_zero χ η θ a b V

end

end ArtinMatthews.VaryingKummerAnalytic
