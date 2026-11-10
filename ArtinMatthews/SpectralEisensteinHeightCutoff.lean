module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import ArtinMatthews.SpectralCuspEisensteinSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! An actual smooth cutoff of normalized source-cusp height. -/
noncomputable section
open Set Filter
open scoped MatrixGroups Topology ContDiff
namespace ArtinMatthews

def eisensteinHeightCutoff (t : ℝ) : ℝ := Real.smoothTransition (t-1)

theorem eisensteinHeightCutoff_contDiff : ContDiff ℝ ∞ eisensteinHeightCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem eisensteinHeightCutoff_range (t : ℝ) :
    0 ≤ eisensteinHeightCutoff t ∧ eisensteinHeightCutoff t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem eisensteinHeightCutoff_zero {t : ℝ} (ht : t ≤ 1) : eisensteinHeightCutoff t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem eisensteinHeightCutoff_one {t : ℝ} (ht : 2 ≤ t) : eisensteinHeightCutoff t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem eisensteinHeightCutoff_nonzero {t : ℝ} (ht : eisensteinHeightCutoff t ≠ 0) : 1 < t := by
  by_contra h
  exact ht (eisensteinHeightCutoff_zero (not_lt.mp h))

theorem eisensteinHeightCutoff_deriv_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) :
    deriv eisensteinHeightCutoff t=0 := by
  rcases ht with ht | ht
  · have he : eisensteinHeightCutoff =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with u hu
      exact eisensteinHeightCutoff_zero hu.le
    rw [he.deriv_eq,deriv_const]
  · have he : eisensteinHeightCutoff =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      exact eisensteinHeightCutoff_one hu.le
    rw [he.deriv_eq,deriv_const]

theorem eisensteinHeightCutoff_second_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) :
    deriv (deriv eisensteinHeightCutoff) t=0 := by
  rcases ht with ht | ht
  · have he : deriv eisensteinHeightCutoff =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with u hu
      exact eisensteinHeightCutoff_deriv_zero (Or.inl hu)
    rw [he.deriv_eq,deriv_const]
  · have he : deriv eisensteinHeightCutoff =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      exact eisensteinHeightCutoff_deriv_zero (Or.inr hu)
    rw [he.deriv_eq,deriv_const]

def cuspEisensteinNormalizedHeight (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : ℝ :=
  cuspEisensteinRowHeight N r a v z/(gamma0CuspTrueWidth N a:ℝ)

theorem cuspEisensteinNormalizedHeight_pos (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    0 < cuspEisensteinNormalizedHeight N r a v z :=
  div_pos (cuspEisensteinRowHeight_pos N r a v z)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N a)

theorem cuspEisensteinNormalizedHeight_power (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (s : ℂ) (z : UpperHalfPlane) :
    (cuspEisensteinNormalizedHeight N r a v z:ℂ)^s=
      (gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowTerm N r a s v z := by
  rw [cuspEisensteinNormalizedHeight,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (cuspEisensteinRowHeight_pos N r a v z).le (by positivity),
    cuspEisensteinRowTerm,Complex.cpow_neg,div_eq_mul_inv]
  simp only [Complex.ofReal_natCast]
  ring

def cuspEisensteinCutoffTerm (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : ℂ :=
  (eisensteinHeightCutoff (cuspEisensteinNormalizedHeight N r a v z):ℂ)*
    (cuspEisensteinNormalizedHeight N r a v z:ℂ)^s

def gamma0CuspEisensteinCutoff (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (z : UpperHalfPlane) : ℂ :=
  (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N 1 a, cuspEisensteinCutoffTerm N 1 a s v z

def gamma0CuspEisensteinRemainder (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (z : UpperHalfPlane) : ℂ := gamma0CuspEisenstein N a s z-gamma0CuspEisensteinCutoff N a s z

theorem cuspEisensteinCutoffTerm_norm_le (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    ‖cuspEisensteinCutoffTerm N r a s v z‖ ≤
      (gamma0CuspTrueWidth N a:ℝ)^(-s.re)*‖cuspEisensteinRowTerm N r a s v z‖ := by
  unfold cuspEisensteinCutoffTerm
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (eisensteinHeightCutoff_range _).1,cuspEisensteinNormalizedHeight_power,norm_mul,
    Complex.norm_natCast_cpow_of_pos (gamma0CuspTrueWidth_pos N a)]
  have he : (-s).re= -s.re := rfl
  rw [he]
  exact mul_le_of_le_one_left (by positivity) (eisensteinHeightCutoff_range _).2

theorem cuspEisensteinCutoffTerm_summable_norm (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a => ‖cuspEisensteinCutoffTerm N r a s v z‖) :=
  ((cuspEisensteinRowTerm_summable_norm N r a s hs z).mul_left _).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => cuspEisensteinCutoffTerm_norm_le N r a s v z)

end ArtinMatthews
