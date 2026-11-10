module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealLog
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Actual arbitrary-ideal-conductor logarithmic derivative bounded uniformly
by an absolute constant times the field degree. Derived from the genuine Euler
logarithm by Cauchy, with no modulus restriction or presumed L-function bound. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open Set Filter Metric
open scoped Topology NumberField
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem dirichlet_logDeriv_eq_deriv_eulerLog {s : ℂ} (hs : 1 < s.re) :
    logDeriv ψ.dirichlet s = deriv ψ.eulerLog s := by
  have hg : DifferentiableAt ℂ ψ.eulerLog s :=
    ψ.eulerLog_differentiableOn.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have heq : ψ.dirichlet =ᶠ[𝓝 s] (fun z : ℂ => Complex.exp (ψ.eulerLog z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (ψ.exp_eulerLog_eq_dirichlet hz).symm
  rw [logDeriv_apply, heq.deriv_eq, (hg.hasDerivAt.cexp).deriv,
    ← ψ.exp_eulerLog_eq_dirichlet hs]
  field_simp [Complex.exp_ne_zero]

/-- The constant is the same explicit universal constant as for Dedekind
zeta, and is independent of the actual ray character and its modulus. -/
theorem dirichlet_logDeriv_norm_le {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖logDeriv ψ.dirichlet s‖ ≤
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
  have hdc : DiffContOnCl ℂ ψ.eulerLog (ball s (1 / 4 : ℝ)) :=
    ψ.eulerLog_differentiableOn.diffContOnCl_ball hsub
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hdc (fun z hz =>
      ψ.eulerLog_norm_le (hRe z (sphere_subset_closedBall hz)))
  rw [ψ.dirichlet_logDeriv_eq_deriv_eulerLog (by linarith)]
  calc
    _ ≤ ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant) / (1 / 4) := h
    _ = dedekindLogDerivUniformConstant * (Module.finrank ℚ K : ℝ) := by
      unfold dedekindLogDerivUniformConstant
      ring

end EvenIdealRayCharacter

theorem exists_evenIdealRayDirichlet_logDeriv_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (M : Ideal (𝓞 K))
      (ψ : EvenIdealRayCharacter K M) (s : ℂ), (3 / 2 : ℝ) ≤ s.re →
      ‖logDeriv ψ.dirichlet s‖ ≤ C * (Module.finrank ℚ K : ℝ) := by
  refine ⟨dedekindLogDerivUniformConstant, dedekindLogDerivUniformConstant_pos, ?_⟩
  intro K _ _ M ψ s hs
  exact ψ.dirichlet_logDeriv_norm_le hs

end
end ArtinMatthews.VaryingKummerAnalytic
