module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! A literal smooth modulus cutoff with support `(3,6)` and plateau `[4,5]`. -/

noncomputable section
namespace ArtinMatthews
open scoped ContDiff Topology

def circleSmoothBump : ContDiffBump (9/2 : ℝ) where
  rIn := 1/2
  rOut := 3/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def circleSmoothCutoff (x : ℝ) : ℝ := circleSmoothBump x

theorem circleSmoothCutoff_contDiff : ContDiff ℝ ∞ circleSmoothCutoff :=
  circleSmoothBump.contDiff

theorem circleSmoothCutoff_compact : HasCompactSupport circleSmoothCutoff :=
  circleSmoothBump.hasCompactSupport

theorem circleSmoothCutoff_nonneg (x : ℝ) : 0 ≤ circleSmoothCutoff x :=
  circleSmoothBump.nonneg

theorem circleSmoothCutoff_le_one (x : ℝ) : circleSmoothCutoff x ≤ 1 :=
  circleSmoothBump.le_one

theorem circleSmoothCutoff_one {x : ℝ} (hx : 4 ≤ x ∧ x ≤ 5) :
    circleSmoothCutoff x = 1 := by
  apply circleSmoothBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |x - 9/2| ≤ 1/2
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem circleSmoothCutoff_support :
    Function.support circleSmoothCutoff = Set.Ioo 3 6 := by
  change Function.support (circleSmoothBump : ℝ → ℝ) = _
  rw [circleSmoothBump.support_eq]
  ext x
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  change (- (3/2 : ℝ) < x - 9/2 ∧ x - 9/2 < 3/2) ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

def circleSmoothScaled (L x : ℝ) : ℝ := circleSmoothCutoff (x / L)

def circleSmoothWeight (L q : ℕ) : ℝ := circleSmoothScaled L q

theorem circleSmoothScaled_contDiff (L : ℝ) : ContDiff ℝ ∞ (circleSmoothScaled L) :=
  circleSmoothCutoff_contDiff.comp (contDiff_id.div_const L)

theorem circleSmoothScaled_support {L : ℝ} (hL : 0 < L) :
    Function.support (circleSmoothScaled L) = Set.Ioo (3*L) (6*L) := by
  ext x
  change (x/L ∈ Function.support circleSmoothCutoff) ↔ _
  rw [circleSmoothCutoff_support]
  exact and_congr (lt_div_iff₀ hL) (div_lt_iff₀ hL)

theorem circleSmoothWeight_nonneg (L q : ℕ) : 0 ≤ circleSmoothWeight L q :=
  circleSmoothCutoff_nonneg _

theorem circleSmoothWeight_le_one (L q : ℕ) : circleSmoothWeight L q ≤ 1 :=
  circleSmoothCutoff_le_one _

theorem circleSmoothWeight_plateau {L q : ℕ} (hL : 0 < L)
    (hqlow : 4*L ≤ q) (hqhigh : q ≤ 5*L) : circleSmoothWeight L q = 1 := by
  apply circleSmoothCutoff_one
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · apply (le_div_iff₀ hLR).mpr
    exact_mod_cast hqlow
  · apply (div_le_iff₀ hLR).mpr
    exact_mod_cast hqhigh

/-- Every derivative has the usual reciprocal-scale normalization. -/
theorem circleSmoothScaled_iteratedDeriv (n : ℕ) (L x : ℝ) :
    iteratedDeriv n (circleSmoothScaled L) x =
      (L⁻¹)^n * iteratedDeriv n circleSmoothCutoff (x/L) := by
  change iteratedDeriv n (fun y => circleSmoothCutoff (y/L)) x = _
  have h := congrFun (iteratedDeriv_comp_const_mul (f := circleSmoothCutoff)
    (circleSmoothBump.contDiff : ContDiff ℝ n circleSmoothCutoff) L⁻¹) x
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The constants depend only on the derivative order, uniformly in every
positive scale and every real argument. -/
theorem circleSmoothScaled_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ x : ℝ,
      ‖iteratedDeriv n (circleSmoothScaled L) x‖ ≤ C * (L⁻¹)^n := by
  obtain ⟨C, hC, hbound⟩ := circleSmoothCutoff_compact.exists_bound_iteratedFDeriv
    circleSmoothCutoff_contDiff n
  refine ⟨C+1, by linarith, fun L hL x => ?_⟩
  have hder : ‖iteratedDeriv n circleSmoothCutoff (x/L)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound n le_rfl (x/L)
  rw [circleSmoothScaled_iteratedDeriv, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)]
  have hmul := mul_le_mul_of_nonneg_left hder (by positivity : 0 ≤ (L⁻¹)^n)
  nlinarith [pow_nonneg (inv_nonneg.mpr hL.le) n]

end ArtinMatthews
