module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroSum
public import ArtinMatthews.VaryingKummerAnalyticMixedXiNormBound
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Field-uniform absolute zero-sum bound for the actual smooth Mellin kernel. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped ContDiff BigOperators
noncomputable section
universe u

theorem mixedCompletedDedekindXi_mellin_power_zero_uniform
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ x : ℝ, 0 < x →
      Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ‖) ≤ C*max 1 x*
          (Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨A,hA,hzero⟩ := mixedCompletedDedekindXi_mellin_power_zero_sum f hcompact hpositive hsmooth
  obtain ⟨B,hB,hbase⟩ := exists_mixedCompletedDedekindXi_height_norm_bound.{u}
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨A*B*(1+Real.log 2),by positivity,?_⟩
  intro K _ _ x hx
  obtain ⟨hs,hbound⟩ := hzero K x hx
  refine ⟨hs,?_⟩
  have hnorm : ‖logDeriv (mixedCompletedDedekindXi K) 2‖ ≤
      B*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)*Real.log 2) := by
    have H := hbase K 0
    rw [show (⟨2,0⟩ : ℂ) = 2 by apply Complex.ext <;> norm_num] at H
    simpa using H
  have hre := (Complex.re_le_norm (logDeriv (mixedCompletedDedekindXi K) 2)).trans hnorm
  have hD := discr_log_nonneg K
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have hscale : Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)*Real.log 2 ≤
      (1+Real.log 2)*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
    nlinarith [mul_nonneg hl hD]
  have hm : 0 ≤ max (1 : ℝ) x := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  calc
    _ ≤ A*max 1 x*(logDeriv (mixedCompletedDedekindXi K) 2).re := hbound
    _ ≤ A*max 1 x*(B*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)*Real.log 2)) :=
      mul_le_mul_of_nonneg_left hre (mul_nonneg hA.le hm)
    _ ≤ A*max 1 x*(B*((1+Real.log 2)*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale hB.le) (mul_nonneg hA.le hm)
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
