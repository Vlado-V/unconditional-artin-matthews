module

public import ArtinMatthews.SpectralEisensteinVerticalCutoff
public import ArtinMatthews.SpectralBoundedExponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
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

/-! Clamping the log only outside a fixed compact height range gives a
genuine entire Banach-valued extension of the cutoff height monomial. -/
noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace ArtinMatthews

section
variable {X : Type*} [TopologicalSpace X]

def spectralBoundedHeightLog (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z) (M : ℝ)
    (hM : 1≤M) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (max 0 (min (Real.log M) (Real.log (H z))):ℝ))
    (Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min
      (hH.log (fun z => (hp z).ne'))))) (Real.log M) (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      exact max_le (Real.log_nonneg hM) (min_le_left _ _))

theorem spectralBoundedHeightLog_eq (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z)
    (M : ℝ) (hM : 1≤M) (z : X) (hz : H z∈Icc 1 M) :
    spectralBoundedHeightLog H hH hp M hM z=(Real.log (H z):ℂ) := by
  change ((max 0 (min (Real.log M) (Real.log (H z))):ℝ):ℂ)=(Real.log (H z):ℂ)
  rw [min_eq_right (Real.log_le_log (hp z) hz.2),max_eq_right (Real.log_nonneg hz.1)]

def spectralBoundedHeightCutoff (H : X → ℝ) (hH : Continuous H) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (eisensteinHeightCutoff (H z):ℂ))
    (Complex.continuous_ofReal.comp (eisensteinHeightCutoff_contDiff.continuous.comp hH)) 1
    (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (eisensteinHeightCutoff_range (H z)).1]
      exact (eisensteinHeightCutoff_range (H z)).2)

def spectralCompactCutoffExponential (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z) (M : ℝ)
    (hM : 1≤M) (s : ℂ) : X →ᵇ ℂ :=
  spectralBoundedHeightCutoff H hH * spectralBoundedExponential (spectralBoundedHeightLog H hH hp M hM) s

theorem spectralCompactCutoffExponential_analyticAt (H : X → ℝ) (hH : Continuous H)
    (hp : ∀ z, 0<H z) (M : ℝ) (hM : 1≤M) (s : ℂ) :
    AnalyticAt ℂ (spectralCompactCutoffExponential H hH hp M hM) s :=
  analyticAt_const.mul (spectralBoundedExponential_analyticAt _ s)

theorem spectralCompactCutoffExponential_eq (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z)
    (M : ℝ) (hM : 1≤M) (s : ℂ) (z : X) (hz : H z≤M) :
    spectralCompactCutoffExponential H hH hp M hM s z=eisensteinVerticalCutoffMode s (H z) := by
  change (eisensteinHeightCutoff (H z):ℂ)*
    spectralBoundedExponential (spectralBoundedHeightLog H hH hp M hM) s z=
    (eisensteinHeightCutoff (H z):ℂ)*(H z:ℂ)^s
  by_cases hlo : H z≤1
  · rw [eisensteinHeightCutoff_zero hlo,Complex.ofReal_zero,zero_mul,zero_mul]
  · rw [spectralBoundedExponential_apply,
      spectralBoundedHeightLog_eq H hH hp M hM z ⟨(lt_of_not_ge hlo).le,hz⟩,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp z).ne'),
      ← Complex.ofReal_log (hp z).le,mul_comm s]

end
end ArtinMatthews
