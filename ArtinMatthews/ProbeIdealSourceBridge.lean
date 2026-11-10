module

public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeGoodBadSourceBridge
public import ArtinMatthews.ProbeIdealRawSeries
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

/-! A single literal source summand for the good and bad local calculations. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealRawTerm_eq_source (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ ξ w z : ℂ)
    (e : Bool) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    probeIdealRawTerm K P χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
      (ArtinMatthews.probeLocalV Q z) (e, l, k, m) =
      probeIdealSourceTerm K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) θ ξ w z (probeBoolFinTwo e) l k m := by
  let Q : ℝ := Ideal.absNorm (P.asIdeal)
  let γ := probeIdealGaussGamma K P χ 2
  let ν := probeIdealGaussLocalVartheta K P χ η
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot)
  have hq : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hA : probeBadFirstParameter Q γ ν θ ξ =
      γ * ν * θ⁻¹ * ((Real.sqrt Q : ℂ)⁻¹ * (Q : ℂ) ^ (-ξ)) := by
    rw [probe_sqrt_cpow_factor Q hQ ξ]
    rfl
  have hB : probeBadThetaParameter Q ν θ ξ =
      ν ^ 3 * (θ⁻¹) ^ 3 * ((Q : ℂ)⁻¹ * ((Q : ℂ) ^ (-ξ)) ^ 3) := by
    rw [probe_cube_cpow_factor _ hq ξ]
    rfl
  dsimp only
  rw [← probeIdealSourceWeight_eq_source K P χ 0 γ ν θ ξ w z (probeBoolFinTwo e) l k m]
  change _ = probeIdealSourceWeight K P χ 0 (probeBadFirstParameter Q γ ν θ ξ)
    (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
    (ArtinMatthews.probeLocalV Q z) (probeBoolFinTwo e) l k m
  rw [hA, hB]
  unfold probeIdealRawTerm probeIdealSourceWeight probeLocalIndexDegree
  simp only [probeBoolFinTwo_val, zero_add, ArtinMatthews.probeLocalW,
    Complex.ofReal_natCast]
  dsimp only [Q, γ, ν]
  simp only [Complex.ofReal_natCast, pow_add, pow_mul, mul_pow]
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
