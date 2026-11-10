module

public import ArtinMatthews.PrincipalDedekindReciprocal
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

/-! The reciprocal naturally supplied by the principal Euler/Möbius source.
It is `(s-1)` times the filled regularized reciprocal, including at the pole. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def principalSourceReciprocal (s : ℂ) : ℂ := (mixedDedekindZeta K s)⁻¹

theorem principalSourceReciprocal_eq_exp_neg_eulerLog {s : ℂ} (hs : 1 < s.re) :
    principalSourceReciprocal K s = Complex.exp (-dedekindEulerLog K s) := by
  rw [principalSourceReciprocal, mixedDedekindZeta_eq K hs,
    ← exp_dedekindEulerLog_eq_dedekindZeta K hs, Complex.exp_neg]

def principalSourceReciprocalBound : ℝ :=
  Real.exp ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant)

theorem principalSourceReciprocalBound_pos : 0 < principalSourceReciprocalBound K :=
  Real.exp_pos _

theorem principalSourceReciprocal_norm_le {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖principalSourceReciprocal K s‖ ≤ principalSourceReciprocalBound K := by
  rw [principalSourceReciprocal_eq_exp_neg_eulerLog K (by linarith), Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr := Complex.re_le_norm (-dedekindEulerLog K s)
  simp only [Complex.neg_re, norm_neg] at hr
  exact hr.trans (dedekindEulerLog_norm_le K hs)

theorem principalSourceReciprocal_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (principalSourceReciprocal K) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hn : mixedDedekindZeta K s ≠ 0 := by
    rw [mixedDedekindZeta_eq K hs, ← exp_dedekindEulerLog_eq_dedekindZeta K hs]
    exact Complex.exp_ne_zero _
  exact ((mixedDedekindZeta_analyticAt K hs1).inv hn).differentiableAt

theorem principalSourceReciprocal_analyticAt_one :
    AnalyticAt ℂ (principalSourceReciprocal K) 1 :=
  mixedDedekindZeta_inv_analyticAt_one K

theorem principalSourceReciprocal_one : principalSourceReciprocal K 1 = 0 :=
  mixedDedekindZeta_inv_one K

theorem principalSourceReciprocal_eq_regularized (s : ℂ) :
    principalSourceReciprocal K s = (s-1) * principalDedekindReciprocal K s :=
  mixedDedekindZeta_inv_eq_regularized K s

end
end ArtinMatthews.VaryingKummerAnalytic
