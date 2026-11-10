module

public import ArtinMatthews.MarkedMajorFourierWeight
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! A scale-free weighted mean from actual unit-interval local means.
Boundedness is used only to establish integrability, never for the final bound. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory Set
open scoped BigOperators

def markedMajorLocalMeanSequence (k : ℤ) : ℝ := ((1+|(k : ℝ)|)^2)⁻¹

theorem markedMajorLocalMeanSequence_nonneg (k : ℤ) :
    0 ≤ markedMajorLocalMeanSequence k := by unfold markedMajorLocalMeanSequence; positivity

theorem markedMajorLocalMeanSequence_summable : Summable markedMajorLocalMeanSequence := by
  have hn : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv (p:=2)).mpr (by norm_num)
  have hs : Summable (fun n : ℕ => ((1+(n : ℝ))^2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using (summable_nat_add_iff 1).mpr hn
  apply Summable.of_nat_of_neg
  · simpa [markedMajorLocalMeanSequence] using hs
  · simpa [markedMajorLocalMeanSequence] using hs

def markedMajorLocalMeanConstant : ℝ := 1+4*∑' k : ℤ, markedMajorLocalMeanSequence k

theorem markedMajorLocalMeanConstant_pos : 0 < markedMajorLocalMeanConstant := by
  have h : 0 ≤ ∑' k : ℤ, markedMajorLocalMeanSequence k :=
    tsum_nonneg markedMajorLocalMeanSequence_nonneg
  unfold markedMajorLocalMeanConstant
  linarith

theorem markedMajorFourierWeight_continuous {W : ℝ} (hW : 0 < W) (n : ℕ) :
    Continuous (markedMajorFourierWeight W n) := by
  unfold markedMajorFourierWeight
  exact ((continuous_const.add (continuous_abs.div_const W)).pow n).inv₀
    (fun t => pow_ne_zero n (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (abs_nonneg t) hW.le))))

theorem markedMajorLocalMean_weight_on_interval (k : ℤ) {t : ℝ}
    (ht : t ∈ Icc (k : ℝ) (k+1)) :
    markedMajorFourierWeight 1 2 t ≤ 4*markedMajorLocalMeanSequence k := by
  have hd : |(k : ℝ)-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hk : |(k : ℝ)| ≤ |t|+1 := by
    calc
      _ = |t+((k : ℝ)-t)| := by congr 1; ring
      _ ≤ |t|+|(k : ℝ)-t| := by simpa only [Real.norm_eq_abs] using norm_add_le t ((k:ℝ)-t)
      _ ≤ _ := add_le_add le_rfl hd
  simp only [markedMajorFourierWeight, div_one, markedMajorLocalMeanSequence]
  rw [← div_eq_mul_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [abs_nonneg t, abs_nonneg (k:ℝ), sq_nonneg (|t|+1-|(k:ℝ)|)]

theorem markedMajorLocalMean_weighted_integrable
    (Q : ℝ → ℂ) (hQ : Continuous Q) (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) :
    Integrable (fun t : ℝ => markedMajorFourierWeight 1 2 t * ‖Q t‖^2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (Q 0)).trans (hB 0)
  apply (markedMajorFourierWeight_integrable_base.mul_const (B^2)).mono'
  · exact ((markedMajorFourierWeight_continuous (by norm_num) 2).mul (hQ.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (markedMajorFourierWeight_nonneg (by norm_num) 2 t) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (by nlinarith [hB t, norm_nonneg (Q t)])
        (markedMajorFourierWeight_nonneg (by norm_num) 2 t))

theorem markedMajorLocalMean_unit (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ a : ℝ, (∫ t in Icc a (a+1), ‖Q t‖^2) ≤ M) :
    (∫ t : ℝ, markedMajorFourierWeight 1 2 t * ‖Q t‖^2) ≤
      markedMajorLocalMeanConstant*M := by
  have hi := markedMajorLocalMean_weighted_integrable Q hQ B hB
  have hsum := hi.hasSum_intervalIntegral 0
  have hf := hQ.norm.pow 2
  have hw := (markedMajorFourierWeight_continuous (W:=1) (by norm_num) 2).mul hf
  have he (k : ℤ) :
      (∫ t in (0 : ℝ)+k..0+k+1, markedMajorFourierWeight 1 2 t*‖Q t‖^2) ≤
        (4*markedMajorLocalMeanSequence k)*M := by
    simp only [zero_add]
    calc
      _ ≤ ∫ t in (k : ℝ)..k+1, (4*markedMajorLocalMeanSequence k)*‖Q t‖^2 :=
        intervalIntegral.integral_mono_on (by linarith) (hw.intervalIntegrable _ _)
          ((continuous_const.mul hf).intervalIntegrable _ _) (fun t ht =>
            mul_le_mul_of_nonneg_right (markedMajorLocalMean_weight_on_interval k ht) (sq_nonneg _))
      _ = (4*markedMajorLocalMeanSequence k)*(∫ t in Icc (k : ℝ) (k+1), ‖Q t‖^2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith),
          ← integral_Icc_eq_integral_Ioc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlocal k)
        (mul_nonneg (by norm_num) (markedMajorLocalMeanSequence_nonneg k))
  calc
    _ = ∑' k : ℤ, ∫ t in (0 : ℝ)+k..0+k+1,
        markedMajorFourierWeight 1 2 t*‖Q t‖^2 := hsum.tsum_eq.symm
    _ ≤ ∑' k : ℤ, (4*markedMajorLocalMeanSequence k)*M :=
      hsum.summable.tsum_le_tsum he ((markedMajorLocalMeanSequence_summable.mul_left 4).mul_right M)
    _ = (4*∑' k : ℤ, markedMajorLocalMeanSequence k)*M := by rw [tsum_mul_right, tsum_mul_left]
    _ ≤ _ := by unfold markedMajorLocalMeanConstant; nlinarith

end ArtinMatthews
