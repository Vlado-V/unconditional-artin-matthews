module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeries
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

/-! The actual Dedekind-zeta logarithmic derivative has nonpositive real part
on the real half-line above one, directly from its positive ideal series. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open Set
open OAI.PrimeDegreePackets
open scoped NumberField BigOperators

private lemma realDedekindTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (m : ℕ) : 0 ≤ realDirichletTerm (idealCoefficientReal K) s m :=
  div_nonneg (idealCoefficientReal_nonneg K m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)

def realDedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℝ) : ℝ :=
  (NumberField.dedekindZeta K (s : ℂ)).re

theorem dedekindZeta_real_eq_terms (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (NumberField.dedekindZeta K s).re =
      ∑' m : ℕ, realDirichletTerm (idealCoefficientReal K) s m := by
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm

theorem dedekindZeta_real_one_le (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 1 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  have h := (idealCoefficient_real_summable K hs).le_tsum 1
    (fun m _ => realDedekindTerm_nonneg K s m)
  simpa [realDirichletTerm, idealCoefficientReal, idealCoefficient_one] using h

theorem dedekindZeta_real_antitone (K : Type*) [Field K] [NumberField K]
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    (NumberField.dedekindZeta K t).re ≤ (NumberField.dedekindZeta K s).re := by
  simp only [dedekindZeta_real_eq_terms]
  apply Summable.tsum_le_tsum _ (idealCoefficient_real_summable K (hs.trans_le hst))
    (idealCoefficient_real_summable K hs)
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · change idealCoefficientReal K m / (m : ℝ) ^ t ≤ idealCoefficientReal K m / (m : ℝ) ^ s
    exact div_le_div_of_nonneg_left (idealCoefficientReal_nonneg K m)
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) s)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) hst)

theorem dedekindZeta_ofReal (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    NumberField.dedekindZeta K (s : ℂ) = (realDedekindZeta K s : ℂ) := by
  rw [realDedekindZeta, ← idealDirichlet_eq_dedekindZeta K]
  simp

theorem realDedekindZeta_deriv_nonpos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : deriv (realDedekindZeta K) s ≤ 0 := by
  have h : AntitoneOn (realDedekindZeta K) (Ioi 1) := by
    intro x hx y _ hxy
    exact dedekindZeta_real_antitone K hx hxy
  have hh := h.derivWithin_nonpos (x := s)
  rwa [derivWithin_of_isOpen isOpen_Ioi hs] at hh

theorem realDedekindZeta_pos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 0 < realDedekindZeta K s :=
  lt_of_lt_of_le zero_lt_one (dedekindZeta_real_one_le K hs)

theorem dedekindZeta_logDeriv_re (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (NumberField.dedekindZeta K) (s : ℂ)).re =
      deriv (realDedekindZeta K) s / realDedekindZeta K s := by
  have h := (dedekindZeta_analyticOnNhd K (s : ℂ) (by simpa using hs)).differentiableAt.hasDerivAt.real_of_complex
  have hd : deriv (realDedekindZeta K) s =
      (deriv (NumberField.dedekindZeta K) (s : ℂ)).re := h.deriv
  rw [logDeriv_apply, dedekindZeta_ofReal, Complex.div_ofReal_re, hd]

/-- The actual generic Dedekind-zeta sign used in the completed-function
logarithmic derivative estimate. -/
theorem dedekindZeta_logDeriv_re_nonpos (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (NumberField.dedekindZeta K) (s : ℂ)).re ≤ 0 := by
  rw [dedekindZeta_logDeriv_re K hs]
  exact div_nonpos_of_nonpos_of_nonneg (realDedekindZeta_deriv_nonpos K hs)
    (realDedekindZeta_pos K hs).le

end
end ArtinMatthews.VaryingKummerAnalytic
