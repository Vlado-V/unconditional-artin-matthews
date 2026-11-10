module

public import ArtinMatthews.MarkedMajorArcMangoldt
public import ArtinMatthews.MarkedMajorArcSmoothing
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Removal of the concrete smoothing for the actual normalized Mangoldt
coefficients. Only the two endpoint strips contribute to the error. -/
namespace ArtinMatthews

open Finset ArithmeticFunction OAI.TwoPointCorrelations

lemma marked_major_mangoldt_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖markedMajorMangoldt χ t n‖ ≤ Real.log n / n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  have ht : ‖mrtCharacterMangoldtTwist χ n‖ ≤ Real.log n := by
    rw [mrtCharacterMangoldtTwist,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hΛ]
    exact (mul_le_of_le_one_left hΛ (χ.norm_le_one _)).trans vonMangoldt_le_log
  rw [markedMajorMangoldt,norm_mul,Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-(1-(t:ℂ)*Complex.I)).re = -1 := by simp
  rw [hre,Real.rpow_neg_one]
  exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq (by ring)

lemma marked_major_mangoldt_norm_on_interval {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {u v : ℝ} (hu : 0 < u) {n : ℕ}
    (hnlo : u < n) (hnhi : (n:ℝ) ≤ v) :
    ‖markedMajorMangoldt χ t n‖ ≤ Real.log v / u := by
  have hnR : (0:ℝ) < n := hu.trans hnlo
  have hn : 0 < n := by exact_mod_cast hnR
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogs := Real.log_le_log hnR hnhi
  calc
    _ ≤ Real.log n / n := marked_major_mangoldt_norm χ t hn
    _ ≤ Real.log v / n := div_le_div_of_nonneg_right hlogs hnR.le
    _ ≤ Real.log v / u := div_le_div_of_nonneg_left (hlogn.trans hlogs) hu hnlo.le

lemma marked_smoothed_interval_boundary_bound {ε u v M : ℝ}
    (hε : 0 < ε) (hu : 0 < u) (huv : u ≤ v) (hM : 0 ≤ M)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, u < (n:ℝ) → (n:ℝ) < (1+ε)*v → ‖a n‖ ≤ M) :
    ‖(∑ n ∈ S, a n*((markedSmoothedStep ε v n-markedSmoothedStep ε u n : ℝ):ℂ)) -
      ∑ n ∈ S, a n*(if u < (n:ℝ) ∧ (n:ℝ) ≤ v then 1 else 0)‖ ≤
      (ε*(u+v)+2)*M := by
  classical
  have hboundary (x : ℝ) (hux : u ≤ x) (hxv : x ≤ v) :
      (∑ n ∈ S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x), ‖a n‖) ≤
      (ε*x+1)*M := by
    have hx : 0 < x := hu.trans_le hux
    have hh := marked_smoothing_boundary_card hx.le
      (by nlinarith : x ≤ (1+ε)*x) S
    calc
      _ ≤ ∑ _n ∈ S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x), M := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hnS,hnlo,hnhi⟩ := mem_filter.mp hn
        exact ha n hnS (hux.trans_lt hnlo)
          (hnhi.trans_le (mul_le_mul_of_nonneg_left hxv (by positivity)))
      _ = ((S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x)).card : ℝ)*M := by simp
      _ ≤ ((1+ε)*x-x+1)*M := mul_le_mul_of_nonneg_right hh hM
      _ = _ := by ring
  exact ((marked_smoothed_interval_sum_error hε hu huv S a).trans
    (add_le_add (hboundary v huv le_rfl) (hboundary u le_rfl huv))).trans_eq (by ring)

/-- A quantitative boundary error for the actual character Mangoldt sum. -/
theorem marked_major_mangoldt_smoothing_error {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {ε u v : ℝ} (hε : 0 < ε) (hu : 1 ≤ u) (huv : u ≤ v)
    (S : Finset ℕ) :
    ‖(∑ n ∈ S, markedMajorMangoldt χ t n*
        ((markedSmoothedStep ε v n-markedSmoothedStep ε u n : ℝ):ℂ)) -
      ∑ n ∈ S, markedMajorMangoldt χ t n*
        (if u < (n:ℝ) ∧ (n:ℝ) ≤ v then 1 else 0)‖ ≤
      (ε*(u+v)+2)*(Real.log ((1+ε)*v)/u) := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hv1 : 1 ≤ (1+ε)*v := by nlinarith
  apply marked_smoothed_interval_boundary_bound hε hu0 huv
    (div_nonneg (Real.log_nonneg hv1) hu0.le)
  intro n hn hlo hhi
  exact marked_major_mangoldt_norm_on_interval χ t hu0 hlo hhi.le

end ArtinMatthews
