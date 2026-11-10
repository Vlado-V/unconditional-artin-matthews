module

public import ArtinMatthews.MarkedMajorMellinLocalMeanUnit
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
public import ArtinMatthews.MarkedMajorMellinLocalMeanTail
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare


set_option backward.privateInPublic true
@[expose] public section

/-! Translated interval mean squares control the actual comparison
Mellin tail without losing the length of the spectral range. -/
namespace ArtinMatthews
open MeasureTheory Set Finset
open OAI.TwoPointCorrelations
open scoped BigOperators ComplexConjugate
noncomputable section

def giantComparisonMellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ)^(Complex.I*(t : ℂ))

theorem giantComparisonMellinPolynomial_eq_exp (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (t : ℝ) :
    giantComparisonMellinPolynomial S a t =
      mrtExponentialPolynomial S a (fun n => Real.log (n : ℝ)) t := by
  unfold giantComparisonMellinPolynomial mrtExponentialPolynomial
  apply sum_congr rfl
  intro n hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  congr 2
  push_cast
  ring

theorem giantComparisonMellinPolynomial_continuous (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) :
    Continuous (giantComparisonMellinPolynomial S a) := by
  rw [show giantComparisonMellinPolynomial S a =
    mrtExponentialPolynomial S a (fun n => Real.log (n : ℝ)) from
      funext (giantComparisonMellinPolynomial_eq_exp S hS a)]
  exact mrtExponentialPolynomial_continuous _ _ _

private theorem comparison_mellinPhase_norm (t : ℝ) :
    ‖Complex.exp ((t : ℂ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem giantComparisonMellinPolynomial_norm_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (t : ℝ) :
    ‖giantComparisonMellinPolynomial S a t‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  rw [giantComparisonMellinPolynomial_eq_exp S hS a]
  unfold mrtExponentialPolynomial
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul, comparison_mellinPhase_norm, mul_one]

theorem giantComparisonMellinPolynomial_local_mean (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    (∫ t in Set.Icc u (u+X), ‖giantComparisonMellinPolynomial S a t‖^2) ≤
      8*Real.exp 1*(X+(N : ℝ))*∑ n ∈ S, ‖a n‖^2 := by
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := (mem_Ioc.mp (hS hn)).1
  let b (n : ℕ) := conj (a n) * Complex.exp (((-Real.log (n : ℝ))*u : ℝ)*Complex.I)
  let M := mrtExponentialPolynomial S b (fun n => -Real.log (n : ℝ))
  have he (t : ℝ) : conj (giantComparisonMellinPolynomial S a (t+u)) = M t := by
    rw [giantComparisonMellinPolynomial_eq_exp S hSpos a]
    simp only [M, b, mrtExponentialPolynomial, map_sum, map_mul, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I]
    apply sum_congr rfl
    intro n _
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hn (t : ℝ) : ‖giantComparisonMellinPolynomial S a (t+u)‖ = ‖M t‖ := by
    rw [← he, Complex.norm_conj]
  have hM := mrtExponentialPolynomial_continuous S b (fun n => -Real.log (n : ℝ))
  have hb (n : ℕ) : ‖b n‖ = ‖a n‖ := by
    simp only [b, norm_mul, Complex.norm_conj, comparison_mellinPhase_norm, mul_one]
  have hmean := mrt_dirichlet_mean_square_subset S hS b hX
  simp only [hb] at hmean
  calc
    _ = ∫ t in u..u+X, ‖giantComparisonMellinPolynomial S a t‖^2 := by
      rw [intervalIntegral.integral_of_le (by linarith : u ≤ u+X), ← integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0 : ℝ)..X, ‖giantComparisonMellinPolynomial S a (t+u)‖^2 := by
      simpa only [zero_add, add_comm X u] using
        (intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := X)
          (fun t => ‖giantComparisonMellinPolynomial S a t‖^2) u).symm
    _ = ∫ t in (0 : ℝ)..X, ‖M t‖^2 := by simp only [hn]
    _ ≤ ∫ t in -X..X, ‖M t‖^2 := by
      rw [intervalIntegral.integral_of_le hX.le, intervalIntegral.integral_of_le (by linarith : -X ≤ X)]
      have hi : IntegrableOn (fun t => ‖M t‖^2) (Set.Ioc (-X) X) :=
        (hM.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      exact setIntegral_mono_set hi (ae_of_all _ (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun _ ht => ⟨(neg_nonpos.mpr hX.le).trans_lt ht.1,ht.2⟩))
    _ ≤ _ := hmean

theorem giantComparisonMellinPolynomial_weighted_tail (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {X L : ℝ} (hX : 0 < X) (hL : 0 ≤ L)
    (n : ℕ) :
    (∫ t : ℝ in {t | L*X ≤ |t|},
      markedMajorFourierWeight X (n+2) t * ‖giantComparisonMellinPolynomial S a t‖^2) ≤
      ((1+L)^n)⁻¹ *
        (markedMajorLocalMeanConstant * (8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2)) := by
  have hSpos (w : ℕ) (hw : w ∈ S) : 0 < w := (mem_Ioc.mp (hS hw)).1
  have hh := markedMajorLocalMean_weighted_tail (giantComparisonMellinPolynomial S a)
    (giantComparisonMellinPolynomial_continuous S hSpos a) (∑ w ∈ S, ‖a w‖)
    (giantComparisonMellinPolynomial_norm_le S hSpos a) hX
    (show 0 ≤ 8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2 by positivity)
    (mul_nonneg hL hX.le) (giantComparisonMellinPolynomial_local_mean S hS a hX) 0 n
  have he : L*X/X = L := mul_div_cancel_right₀ L hX.ne'
  simpa only [sub_zero, he] using hh

end
end ArtinMatthews
