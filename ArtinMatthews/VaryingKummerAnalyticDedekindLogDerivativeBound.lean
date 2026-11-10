module

public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerLog
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A degree-uniform logarithmic-derivative bound for the actual Dedekind zeta
function, obtained by Cauchy's estimate on its genuine Euler logarithm. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open Set Filter Metric
open scoped Topology

/-- A positive universal constant, independent of the number field. -/
def dedekindLogDerivUniformConstant : ℝ := 4 * dedekindEulerLogConstant

theorem dedekindLogDerivUniformConstant_pos : 0 < dedekindLogDerivUniformConstant :=
  mul_pos (by norm_num) dedekindEulerLogConstant_pos

/-- The genuine Euler logarithm differentiates to the actual logarithmic
derivative of Mathlib's Dedekind zeta function. -/
theorem dedekindZeta_logDeriv_eq_deriv_eulerLog
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (NumberField.dedekindZeta K) s = deriv (dedekindEulerLog K) s := by
  have hg : DifferentiableAt ℂ (dedekindEulerLog K) s :=
    (dedekindEulerLog_differentiableOn K).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have heq : NumberField.dedekindZeta K =ᶠ[𝓝 s]
      (fun z : ℂ => Complex.exp (dedekindEulerLog K z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (exp_dedekindEulerLog_eq_dedekindZeta K hz).symm
  rw [logDeriv_apply, heq.deriv_eq, (hg.hasDerivAt.cexp).deriv,
    ← exp_dedekindEulerLog_eq_dedekindZeta K hs]
  field_simp [Complex.exp_ne_zero]

/-- The actual logarithmic derivative is bounded by a universal constant
times the actual field degree throughout `Re(s)≥3/2`. -/
theorem dedekindZeta_logDeriv_norm_le
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖logDeriv (NumberField.dedekindZeta K) s‖ ≤
      dedekindLogDerivUniformConstant * (Module.finrank ℚ K : ℝ) := by
  have hRe (z : ℂ) (hz : z ∈ closedBall s (1 / 4 : ℝ)) : 5 / 4 ≤ z.re := by
    have hn : ‖s - z‖ ≤ (1 / 4 : ℝ) := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have hr := Complex.re_le_norm (s - z)
    simp only [Complex.sub_re] at hr
    linarith
  have hsub : closedBall s (1 / 4 : ℝ) ⊆ {z : ℂ | 1 < z.re} := by
    intro z hz
    have h := hRe z hz
    change 1 < z.re
    linarith
  have hdc : DiffContOnCl ℂ (dedekindEulerLog K) (ball s (1 / 4 : ℝ)) :=
    (dedekindEulerLog_differentiableOn K).diffContOnCl_ball hsub
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hdc (fun z hz =>
      dedekindEulerLog_norm_le K (hRe z (sphere_subset_closedBall hz)))
  rw [dedekindZeta_logDeriv_eq_deriv_eulerLog K (by linarith)]
  calc
    _ ≤ ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant) / (1 / 4) := h
    _ = dedekindLogDerivUniformConstant * (Module.finrank ℚ K : ℝ) := by
      unfold dedekindLogDerivUniformConstant
      ring

/-- An explicit uniform existential interface for zero-count and contour
applications; no logarithmic-derivative estimate is assumed. -/
theorem exists_dedekindZeta_logDeriv_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (s : ℂ),
      (3 / 2 : ℝ) ≤ s.re →
      ‖logDeriv (NumberField.dedekindZeta K) s‖ ≤ C * (Module.finrank ℚ K : ℝ) := by
  refine ⟨dedekindLogDerivUniformConstant, dedekindLogDerivUniformConstant_pos, ?_⟩
  intro K _ _ s hs
  exact dedekindZeta_logDeriv_norm_le K hs

end
end ArtinMatthews.VaryingKummerAnalytic
