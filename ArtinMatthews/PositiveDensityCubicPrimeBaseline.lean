module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.GiantPrimeShift
public import ArtinMatthews.HeckePrimeSmoothSums
public import ArtinMatthews.HeckeCubicPrimeSmoothLimit
public import ArtinMatthews.MarkedCorrelationNormalization
public import ArtinMatthews.PrimeExtractionTupleBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
meta import Mathlib.Tactic.Linarith.NNRealPreprocessor


set_option backward.privateInPublic true
@[expose] public section

/-! The unweighted prime baseline for the actual cubic theta coefficients.
The finite literal predecessor shift is kept in the test. -/

noncomputable section
namespace ArtinMatthews

open Filter
open OAI OAI.SevenEighths
open scoped BigOperators Topology Asymptotics ContDiff

def giantCubicShiftedPrimeBaseline (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x, (Φ (((p : ℝ) - 1) / x) : ℂ) * χ p * idealThetaCoeff η p

def giantCubicUnshiftedPrimeBaseline (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x, (Φ ((p : ℝ) / x) : ℂ) * χ p * idealThetaCoeff η p

theorem giantCubicUnshiftedPrimeBaseline_eq_hecke (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) {T x : ℝ}
    (hx : 0 < x) (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    giantCubicUnshiftedPrimeBaseline η χ Φ T x =
      heckeRationalPrimeSmoothSum η χ (fun t => (Φ t : ℂ)) x 0 := by
  classical
  unfold heckeRationalPrimeSmoothSum giantCubicUnshiftedPrimeBaseline
  rw [tsum_eq_sum (s := giantPrimeMeanRange T x)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [(Finset.mem_filter.mp hp).2, ite_true, Complex.ofReal_zero, zero_mul,
      Complex.cpow_zero, mul_one]
    ring
  · intro p hp
    by_cases hprime : p.Prime
    · have hzero : Φ ((p : ℝ) / x) = 0 := by
        by_contra hne
        have htop : (p : ℝ) ≤ T * x := ((div_lt_iff₀ hx).mp (hs hne).2).le
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.zero_le p, (Nat.le_floor htop).trans (Nat.le_succ _)⟩, hprime⟩)
      simp only [hprime, ite_true, hzero, Complex.ofReal_zero, mul_zero, zero_mul]
    · simp only [hprime, ite_false]

theorem giantCubicPrimeBaseline_shift_error_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) {K : NNReal} (hΦ : LipschitzWith K Φ)
    {T x : ℝ} (hT : 0 ≤ T) (hx : 1 ≤ x) :
    ‖giantCubicShiftedPrimeBaseline η χ Φ T x - giantCubicUnshiftedPrimeBaseline η χ Φ T x‖ ≤
      2 * (K : ℝ) * (T + 2) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hterm (p : ℕ) : |Φ (((p : ℝ) - 1) / x) - Φ ((p : ℝ) / x)| ≤ (K : ℝ) / x := by
    have h := hΦ.norm_sub_le (((p : ℝ) - 1) / x) ((p : ℝ) / x)
    rw [show ((p : ℝ) - 1) / x - (p : ℝ) / x = -(1 / x) by ring] at h
    simpa only [Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hx₀), mul_one_div] using h
  unfold giantCubicShiftedPrimeBaseline giantCubicUnshiftedPrimeBaseline
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _p ∈ giantPrimeMeanRange T x, 2 * (K : ℝ) / x := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← sub_mul, ← sub_mul, ← Complex.ofReal_sub, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have hχ := χ.norm_le_one (p : ZMod M)
      have hη := idealThetaCoeff_prime_norm_le_two η (Finset.mem_filter.mp hp).2
      calc
        _ ≤ ((K : ℝ) / x * 1) * 2 := mul_le_mul
          (mul_le_mul (hterm p) hχ (norm_nonneg _) (div_nonneg K.2 hx₀.le))
          hη (norm_nonneg _) (mul_nonneg (div_nonneg K.2 hx₀.le) zero_le_one)
        _ = _ := by ring
    _ = (giantPrimeMeanRange T x).card * (2 * (K : ℝ) / x) := by simp
    _ ≤ (T * x + 2) * (2 * (K : ℝ) / x) := mul_le_mul_of_nonneg_right
      (giantPrimeMeanRange_card_bound hT hx₀.le) (by positivity)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hx₀).mpr
      nlinarith [mul_nonneg K.2 (sub_nonneg.mpr hx)]

theorem giantCubicShiftedPrimeBaseline_isLittleO (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    {T : ℝ} (hT : 1 < T) (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    giantCubicShiftedPrimeBaseline (cubicNumeratorHeckeCharacter A hA) χ Φ T
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  let η := cubicNumeratorHeckeCharacter A hA
  let W := fun t : ℝ => (Φ t : ℂ)
  have hW : ContDiff ℝ ∞ W := Complex.ofRealCLM.contDiff.comp hΦ
  have hWs : Function.support W ⊆ Set.Icc 1 T := by
    intro t ht
    exact Set.Ioo_subset_Icc_self (hs (fun hz => ht (by simp [W, hz])))
  have hunshift := cubicNumeratorPrimeSmooth_isLittleO A hA hnoncube χ W 1 T one_pos hWs hW 1
  have heq : (fun x : ℝ => heckeRationalPrimeSmoothSum η χ W x 0) =ᶠ[atTop]
      giantCubicUnshiftedPrimeBaseline η χ Φ T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (giantCubicUnshiftedPrimeBaseline_eq_hecke η χ Φ hx hs).symm
  have hscale : (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))) =ᶠ[atTop]
      (fun x : ℝ => x / Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le, Real.rpow_one, div_eq_mul_inv]
  have hbase := hunshift.congr' heq hscale
  obtain ⟨K, hK⟩ := giant_compact_test_lipschitz Φ
    (hΦ.differentiable (by simp)) (hΦ.continuous_deriv (by simp)) hc
  have herr : (fun x => giantCubicShiftedPrimeBaseline η χ Φ T x -
      giantCubicUnshiftedPrimeBaseline η χ Φ T x) =o[atTop] (fun x : ℝ => x / Real.log x) := by
    apply marked_correlation_isLittleO_of_normalized_norm
    have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mul_const (2 * (K : ℝ) * (T + 2))
    simp only [id_eq, zero_mul] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact mul_nonneg (div_nonneg (Real.log_pos hx).le (by linarith)) (norm_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact mul_le_mul_of_nonneg_left
        (giantCubicPrimeBaseline_shift_error_le η χ Φ hK (by linarith) hx.le)
        (div_nonneg (Real.log_pos hx).le (by linarith))
  exact (herr.add hbase).congr' (Filter.Eventually.of_forall fun _ => sub_add_cancel _ _)
    Filter.EventuallyEq.rfl

end ArtinMatthews
