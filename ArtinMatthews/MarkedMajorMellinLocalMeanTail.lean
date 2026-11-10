module

public import ArtinMatthews.MarkedMajorMellinLocalMeanUnit
public import ArtinMatthews.MarkedMajorMellinLocalMean
public import Mathlib.MeasureTheory.Integral.Bochner.Set
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


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial weighted tails of the local L² mean, with no scale loss. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory Set

theorem markedMajorLocalMean_integrable_higher (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {X : ℝ} (hX : 0 < X) (c : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    Integrable (fun t : ℝ => markedMajorFourierWeight X n (t-c)*‖Q t‖^2) := by
  apply (markedMajorLocalMean_integrable Q hQ B hB hX c).mono'
  · exact (((markedMajorFourierWeight_continuous hX n).comp
      (continuous_id.sub continuous_const)).mul (hQ.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (markedMajorFourierWeight_nonneg hX n (t-c)) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (markedMajorFourierWeight_le_two hX hn (t-c)) (sq_nonneg _))

theorem markedMajorLocalMean_weighted_higher (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hlocal : ∀ a : ℝ, (∫ t in Icc a (a+X), ‖Q t‖^2) ≤ M) (c : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ t : ℝ, markedMajorFourierWeight X n (t-c)*‖Q t‖^2) ≤
      markedMajorLocalMeanConstant*M := by
  apply le_trans _ (markedMajorLocalMean_weighted Q hQ B hB hX hM hlocal c)
  exact integral_mono (markedMajorLocalMean_integrable_higher Q hQ B hB hX c hn)
    (markedMajorLocalMean_integrable Q hQ B hB hX c)
    (fun t => mul_le_mul_of_nonneg_right (markedMajorFourierWeight_le_two hX hn (t-c)) (sq_nonneg _))

theorem markedMajorLocalMean_weighted_tail (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {X M R : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hlocal : ∀ a : ℝ, (∫ t in Icc a (a+X), ‖Q t‖^2) ≤ M)
    (c : ℝ) (n : ℕ) :
    (∫ t : ℝ in {t | R ≤ |t-c|}, markedMajorFourierWeight X (n+2) (t-c)*‖Q t‖^2) ≤
      ((1+R/X)^n)⁻¹*(markedMajorLocalMeanConstant*M) := by
  let K : ℝ := ((1+R/X)^n)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : MeasurableSet {t : ℝ | R ≤ |t-c|} :=
    measurableSet_le measurable_const ((continuous_id.sub continuous_const).abs.measurable)
  have hi := markedMajorLocalMean_integrable Q hQ B hB hX c
  calc
    _ ≤ ∫ t : ℝ in {t | R ≤ |t-c|}, K*(markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) := by
      apply setIntegral_mono_on
        (markedMajorLocalMean_integrable_higher Q hQ B hB hX c (by omega : 2 ≤ n+2)).integrableOn
        (hi.const_mul K).integrableOn hS
      intro t ht
      have hpoint := mul_le_mul_of_nonneg_right
        (markedMajorFourierWeight_tail_pointwise hX hR n ht) (sq_nonneg ‖Q t‖)
      exact hpoint.trans_eq (by dsimp [K]; ring)
    _ ≤ ∫ t : ℝ, K*(markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) :=
      setIntegral_le_integral (hi.const_mul K) (Filter.Eventually.of_forall (fun t =>
        mul_nonneg hK (mul_nonneg (markedMajorFourierWeight_nonneg hX 2 (t-c)) (sq_nonneg _))))
    _ = K*(∫ t : ℝ, markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (markedMajorLocalMean_weighted Q hQ B hB hX hM hlocal c) hK

end ArtinMatthews
