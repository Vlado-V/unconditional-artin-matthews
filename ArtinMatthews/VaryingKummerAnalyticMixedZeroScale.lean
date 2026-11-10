module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.KummerSplittingDiscriminant
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
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

/-! A concrete field-uniform zero-analysis scale, retaining both discriminant
and degree. For the actual varying-prime Kummer fields it is O(q² log q). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem discr_abs_one_le : 1 ≤ |(discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

theorem discr_log_nonneg : 0 ≤ Real.log |(discr K : ℝ)| :=
  Real.log_nonneg (discr_abs_one_le K)

/-- Padding by the actual degree avoids any unproved lower-discriminant input. -/
def mixedZeroScale (C : ℝ) : ℝ :=
  Real.log |(discr K : ℝ)| + 2*C*(Module.finrank ℚ K : ℝ) + 2

theorem mixedZeroScale_two_le {C : ℝ} (hC : 0 ≤ C) : 2 ≤ mixedZeroScale K C := by
  unfold mixedZeroScale
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC) (Nat.cast_nonneg (Module.finrank ℚ K))
  linarith [discr_log_nonneg K]

theorem mixedZeroScale_pos {C : ℝ} (hC : 0 ≤ C) : 0 < mixedZeroScale K C :=
  lt_of_lt_of_le (by norm_num) (mixedZeroScale_two_le K hC)

theorem mixedDiscriminantScale_log_le :
    Real.log (mixedDiscriminantScale K) ≤ Real.log |(discr K : ℝ)|/2 := by
  rw [mixedDiscriminantScale_log]
  have h := mul_nonneg (Nat.cast_nonneg (InfinitePlace.nrComplexPlaces K))
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  linarith

/-- An explicit uniform Kummer bound for every fixed nonnegative Gamma constant. -/
theorem primeKummerField_mixedZeroScale_le {C : ℝ} (hC : 0 ≤ C)
    {a : ℤ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    mixedZeroScale (primeKummerField q a) C ≤
      (6 + (2*C+2)/Real.log 2) * (q : ℝ)^2 * Real.log q := by
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hl2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlq : Real.log (2:ℝ) ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hd : (Module.finrank ℚ (primeKummerField q a) : ℝ) ≤ (q : ℝ)^2 := by
    rw [finrank_primeKummerField_of_large_prime ha0 ha1 ham1 hq haq]
    exact_mod_cast (show q*(q-1) ≤ q^2 by nlinarith [Nat.sub_le q 1])
  have hqSq : (1:ℝ) ≤ (q : ℝ)^2 := by nlinarith
  have hterm : 2*C*(Module.finrank ℚ (primeKummerField q a) : ℝ)+2 ≤
      ((2*C+2)/Real.log 2) * (q : ℝ)^2 * Real.log q := by
    calc
      _ ≤ (2*C+2)*(q : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*C)]
      _ = ((2*C+2)/Real.log 2) * (q : ℝ)^2 * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlq (by positivity)
  unfold mixedZeroScale
  have hdisc := primeKummerField_log_discr_le ha0 ha1 ham1 hq haq
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
