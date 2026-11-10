module

public import ArtinMatthews.ProbeIdealGaussPhase
public import ArtinMatthews.ProbeIdealLocalCoefficient
public import ArtinMatthews.ProbeLocalSurvivorIndex
public import ArtinMatthews.ProbeIdealSurvivorIndex
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

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealRawTerm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex) : ℂ :=
  let e : ℕ := if i.1 then 1 else 0
  let t := probeLocalIndexDegree i
  let q : ℂ := Ideal.absNorm (P.asIdeal)
  let σ : ℂ := Real.sqrt (Ideal.absNorm (P.asIdeal))
  let γ := probeIdealGaussGamma K P χ 2
  let v := probeIdealGaussLocalVartheta K P χ η
  γ ^ e * v ^ t * (θ⁻¹) ^ t * (σ⁻¹) ^ e * (q⁻¹) ^ i.2.1 * a ^ t *
    (θ * b) ^ i.2.2.1 * V ^ i.2.2.2 *
      probeIdealLocalCoefficient K P χ t i.2.2.1 (6 * i.2.2.2)

def probeIdealRawLocalSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ) : ℂ :=
  ∑' i : ProbeLocalRawIndex, probeIdealRawTerm K P χ η θ a b V i

theorem probeIdealRawTerm_zero_of_coefficient (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex)
    (hc : probeIdealLocalCoefficient K P χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0) :
    probeIdealRawTerm K P χ η θ a b V i = 0 := by
  simp only [probeIdealRawTerm, hc, mul_zero]

theorem probeIdealRawLocalSeries_reindex (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (η θ a b V : ℂ) :
    probeIdealRawLocalSeries K P χ η θ a b V =
      ∑' j : ProbeLocalSurvivor,
        probeIdealRawTerm K P χ η θ a b V (probeLocalSurvivorIndex j) := by
  apply probeIdeal_supported_tsum K P χ hχ hminus
  exact probeIdealRawTerm_zero_of_coefficient K P χ η θ a b V

end

end ArtinMatthews.VaryingKummerAnalytic
