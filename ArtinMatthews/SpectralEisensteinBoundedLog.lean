module

public import ArtinMatthews.SpectralBoundedExponential
public import ArtinMatthews.SpectralCuspTrueWidth
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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

/-! A bounded continuous logarithm agreeing with the actual source-height
logarithm throughout the compact forcing band [1,2]. -/
noncomputable section
open Set
open scoped MatrixGroups BoundedContinuousFunction
namespace ArtinMatthews

def eisensteinClampedLog (t : ℝ) : ℝ := max 0 (min (Real.log 2) (Real.log t))

theorem eisensteinClampedLog_bounds (t : ℝ) :
    0 ≤ eisensteinClampedLog t ∧ eisensteinClampedLog t ≤ Real.log 2 := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact ⟨le_max_left _ _,max_le h2 (min_le_left _ _)⟩

theorem eisensteinClampedLog_eq {t : ℝ} (ht : t ∈ Icc (1:ℝ) 2) :
    eisensteinClampedLog t=Real.log t := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht.1
  have h2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith [ht.1]) ht.2
  rw [eisensteinClampedLog,min_eq_right h2,max_eq_right h0]

def gamma0SourceHeight (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (z : UpperHalfPlane) : ℝ :=
  (a • z).im/(gamma0CuspTrueWidth N a:ℝ)

theorem gamma0SourceHeight_pos (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (z : UpperHalfPlane) :
    0 < gamma0SourceHeight N a z :=
  div_pos (a • z).im_pos (by exact_mod_cast gamma0CuspTrueWidth_pos N a)

theorem gamma0SourceHeight_continuous (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Continuous (gamma0SourceHeight N a) := by
  change Continuous (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.mapGL ℝ a • z).im/(gamma0CuspTrueWidth N a:ℝ))
  exact (UpperHalfPlane.continuous_im.comp (continuous_const_smul _)).div_const _

def gamma0SourceBoundedLog (N : ℕ) [NeZero N] (a : SL(2,ℤ)) : UpperHalfPlane →ᵇ ℂ where
  toFun z := (eisensteinClampedLog (gamma0SourceHeight N a z):ℂ)
  continuous_toFun := by
    apply Complex.continuous_ofReal.comp
    exact continuous_const.max (continuous_const.min
      ((gamma0SourceHeight_continuous N a).log (fun z => (gamma0SourceHeight_pos N a z).ne')))
  map_bounded' := by
    refine ⟨2*Real.log 2,?_⟩
    intro x y
    apply (dist_le_norm_add_norm _ _).trans
    have hx := eisensteinClampedLog_bounds (gamma0SourceHeight N a x)
    have hy := eisensteinClampedLog_bounds (gamma0SourceHeight N a y)
    rw [Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hx.1,abs_of_nonneg hy.1]
    linarith

theorem gamma0SourceBoundedLog_eq (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (z : UpperHalfPlane)
    (hz : gamma0SourceHeight N a z ∈ Icc (1:ℝ) 2) :
    gamma0SourceBoundedLog N a z=(Real.log (gamma0SourceHeight N a z):ℂ) :=
  congrArg Complex.ofReal (eisensteinClampedLog_eq hz)

theorem gamma0SourceBoundedExponential_eq (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (z : UpperHalfPlane) (hz : gamma0SourceHeight N a z ∈ Icc (1:ℝ) 2) :
    spectralBoundedExponential (gamma0SourceBoundedLog N a) s z=(gamma0SourceHeight N a z:ℂ)^s := by
  rw [spectralBoundedExponential_apply,gamma0SourceBoundedLog_eq N a z hz,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (gamma0SourceHeight_pos N a z).ne'),
    ← Complex.ofReal_log (gamma0SourceHeight_pos N a z).le]
  congr 1
  ring

end ArtinMatthews
