module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.KummerSplittingDiscriminant
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroHeightBase
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Uniform unit-height zero counting for the actual completed Dedekind zeta.
Every constant is independent of the number field. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open OAI.PrimeDegreePackets.AnalyticGrowth
noncomputable section
universe u

theorem exists_mixedDedekind_zeroHeight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      zeroHeightCount (mixedCompletedDedekindXi K) T ≤
        C * (Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ) * Real.log (|T|+2)) := by
  obtain ⟨B,hB,hbase⟩ := exists_mixedDedekind_zeroHeight_bound_with_logDeriv.{u}
  obtain ⟨E,hE,hzeta⟩ := exists_dedekindZeta_logDeriv_norm_bound.{u}
  let A : ℝ := (15/2+5*E)/Real.log 2
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨B+A+5/2,by positivity,?_⟩
  intro K _ _ T
  have hd : 1 ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (show 1 ≤ Module.finrank ℚ K from Module.finrank_pos)
  have hd0 : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  have hl : Real.log 2 ≤ Real.log (|T|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hl0 : 0 ≤ Real.log (|T|+2) := hl2.le.trans hl
  have hmass : 15/2+5*E*(Module.finrank ℚ K : ℝ) ≤
      A*(Module.finrank ℚ K : ℝ)*Real.log (|T|+2) := by
    calc
      _ ≤ (15/2+5*E)*(Module.finrank ℚ K : ℝ) := by nlinarith
      _ = A*(Module.finrank ℚ K : ℝ)*Real.log 2 := by dsimp [A]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg hA.le hd0)
  have H := hbase K T
  have Hζ := hzeta K (⟨2,T⟩ : ℂ) (by norm_num)
  have hD := discr_log_nonneg K
  have hterm : 0 ≤ (Module.finrank ℚ K : ℝ)*Real.log (|T|+2) := mul_nonneg hd0 hl0
  have hCD : 0 ≤ (B+A)*Real.log |(discr K : ℝ)| := mul_nonneg (by positivity) hD
  nlinarith

theorem exists_primeKummer_zeroHeight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ), q.Prime → a.natAbs ≤ q → ∀ T : ℝ,
        zeroHeightCount (mixedCompletedDedekindXi (primeKummerField q a)) T ≤
          C * (q : ℝ)^2 * Real.log ((q : ℝ)*(|T|+2)) := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedDedekind_zeroHeight_bound
  refine ⟨6*C,by positivity,?_⟩
  intro a ha0 ha1 ham1 q hq haq T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < |T|+2 := by positivity
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hlT : 0 ≤ Real.log (|T|+2) := Real.log_nonneg (by linarith [abs_nonneg T])
  have hn : (Module.finrank ℚ (primeKummerField q a) : ℝ) ≤ (q : ℝ)^2 := by
    rw [finrank_primeKummerField_of_large_prime ha0 ha1 ham1 hq haq]
    exact_mod_cast (show q*(q-1) ≤ q^2 by nlinarith [Nat.sub_le q 1])
  have hd := primeKummerField_log_discr_le ha0 ha1 ham1 hq haq
  have H := hbound (primeKummerField q a) T
  have hnl := mul_le_mul_of_nonneg_right hn hlT
  rw [Real.log_mul hq0.ne' hT0.ne']
  calc
    _ ≤ C*(6*(q : ℝ)^2*Real.log q + (q : ℝ)^2*Real.log (|T|+2)) :=
      H.trans (mul_le_mul_of_nonneg_left (add_le_add hd hnl) hC.le)
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (sq_nonneg (q : ℝ))) hlT]

end
end ArtinMatthews.VaryingKummerAnalytic
