module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.KummerSplittingDiscriminant
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroUniform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Actual varying-prime Kummer specialization of the absolute zero bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped ContDiff BigOperators
noncomputable section

theorem primeKummer_mellin_power_zero_bound
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ), q.Prime → a.natAbs ≤ q → ∀ x : ℝ, 0 < x →
        (∑' ρ, ‖(zeroMultiplicity (mixedCompletedDedekindXi (primeKummerField q a)) ρ : ℂ)*
          mellin f ρ*(x : ℂ)^ρ‖) ≤ C*max 1 x*(q : ℝ)^2*Real.log q := by
  obtain ⟨C,hC,hbound⟩ := mixedCompletedDedekindXi_mellin_power_zero_uniform f hcompact hpositive hsmooth
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C*(6+1/Real.log 2),by positivity,?_⟩
  intro a ha0 ha1 ham1 q hq haq x hx
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hlq : Real.log (2 : ℝ) ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hn : (Module.finrank ℚ (primeKummerField q a) : ℝ) ≤ (q : ℝ)^2 := by
    rw [finrank_primeKummerField_of_large_prime ha0 ha1 ham1 hq haq]
    exact_mod_cast (show q*(q-1) ≤ q^2 by nlinarith [Nat.sub_le q 1])
  have hd := primeKummerField_log_discr_le ha0 ha1 ham1 hq haq
  have hm : 0 ≤ max (1 : ℝ) x := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hlog : (q : ℝ)^2 ≤ (1/Real.log 2)*(q : ℝ)^2*Real.log q := by
    calc
      _ = (1/Real.log 2)*(q : ℝ)^2*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlq (by positivity)
  have hs : Real.log |(discr (primeKummerField q a) : ℝ)|+
      (Module.finrank ℚ (primeKummerField q a) : ℝ) ≤
        (6+1/Real.log 2)*(q : ℝ)^2*Real.log q := by nlinarith
  calc
    _ ≤ C*max 1 x*(Real.log |(discr (primeKummerField q a) : ℝ)|+
        (Module.finrank ℚ (primeKummerField q a) : ℝ)) := (hbound _ x hx).2
    _ ≤ C*max 1 x*((6+1/Real.log 2)*(q : ℝ)^2*Real.log q) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hC.le hm)
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
