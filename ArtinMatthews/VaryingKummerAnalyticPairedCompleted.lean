module

public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The product of an actual completed function and its inverse-character
completion. A single inverse-character functional equation makes the product
self-reflecting; no self-reflection of either factor is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open ArtinMatthews.ReusedGrowth OAI.PrimeDegreePackets.AnalyticGrowth
open Complex
open scoped ComplexConjugate
noncomputable section

def pairedCompleted (F G : ℂ → ℂ) : ℂ → ℂ := fun s => F s * G s

variable {F G : ℂ → ℂ}

theorem pairedCompleted_entire (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    Differentiable ℂ (pairedCompleted F G) := hF.mul hG

theorem pairedCompleted_hasSubquadraticGrowth
    (hF : HasSubquadraticGrowth F) (hG : HasSubquadraticGrowth G) :
    HasSubquadraticGrowth (pairedCompleted F G) := hF.mul hG

theorem pairedCompleted_functionalEquation {W : ℂ}
    (hfe : ∀ s, F s = W * G (1-s)) (s : ℂ) :
    pairedCompleted F G (1-s) = pairedCompleted F G s := by
  have hr : 1-(1-s) = s := by ring
  simp only [pairedCompleted, hfe (1-s), hfe s, hr]
  ring

theorem pairedCompleted_conj (hconj : ∀ s, G (conj s) = conj (F s)) (s : ℂ) :
    pairedCompleted F G (conj s) = conj (pairedCompleted F G s) := by
  have hF : F (conj s) = conj (G s) := by
    simpa only [starRingEnd_self_apply] using (congrArg conj (hconj (conj s))).symm
  simp only [pairedCompleted, hF, hconj s, map_mul]
  ring

theorem pairedCompleted_zero_iff (s : ℂ) :
    pairedCompleted F G s = 0 ↔ F s = 0 ∨ G s = 0 := mul_eq_zero

theorem pairedCompleted_ne_zero_iff (s : ℂ) :
    pairedCompleted F G s ≠ 0 ↔ F s ≠ 0 ∧ G s ≠ 0 := mul_ne_zero_iff

theorem pairedCompleted_ne_zero_right
    (hF : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hG : ∀ s : ℂ, 1 < s.re → G s ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    pairedCompleted F G s ≠ 0 := mul_ne_zero (hF s hs) (hG s hs)

theorem pairedCompleted_zero_strip {W : ℂ}
    (hfe : ∀ s, F s = W * G (1-s))
    (hF : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hG : ∀ s : ℂ, 1 < s.re → G s ≠ 0)
    {s : ℂ} (hs : pairedCompleted F G s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra hn
    have hr : 1 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    exact pairedCompleted_ne_zero_right hF hG hr
      ((pairedCompleted_functionalEquation hfe s).trans hs)
  · by_contra hn
    exact pairedCompleted_ne_zero_right hF hG (lt_of_not_ge hn) hs

theorem pairedCompleted_logDeriv (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {s : ℂ} (hFs : F s ≠ 0) (hGs : G s ≠ 0) :
    logDeriv (pairedCompleted F G) s = logDeriv F s + logDeriv G s := by
  exact logDeriv_fun_mul s hFs hGs (hF s) (hG s)

theorem pairedCompleted_logDeriv_right (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFr : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hGr : ∀ s : ℂ, 1 < s.re → G s ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (pairedCompleted F G) s = logDeriv F s + logDeriv G s :=
  pairedCompleted_logDeriv hF hG (hFr s hs) (hGr s hs)

theorem pairedCompleted_logDeriv_norm_le (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {s : ℂ} (hFs : F s ≠ 0) (hGs : G s ≠ 0) {B C : ℝ}
    (hB : ‖logDeriv F s‖ ≤ B) (hC : ‖logDeriv G s‖ ≤ C) :
    ‖logDeriv (pairedCompleted F G) s‖ ≤ B+C := by
  rw [pairedCompleted_logDeriv hF hG hFs hGs]
  exact (norm_add_le _ _).trans (add_le_add hB hC)

theorem pairedCompleted_analyticOrderAt (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (s : ℂ) :
    analyticOrderAt (pairedCompleted F G) s = analyticOrderAt F s + analyticOrderAt G s :=
  analyticOrderAt_mul (hF.analyticAt s) (hG.analyticAt s)

theorem pairedCompleted_meromorphicOrderAt (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (s : ℂ) :
    meromorphicOrderAt (pairedCompleted F G) s =
      meromorphicOrderAt F s + meromorphicOrderAt G s :=
  meromorphicOrderAt_mul (hF.analyticAt s).meromorphicAt (hG.analyticAt s).meromorphicAt

theorem pairedCompleted_zeroMultiplicity (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h0 : pairedCompleted F G 0 ≠ 0) (s : ℂ) :
    zeroMultiplicity (pairedCompleted F G) s = zeroMultiplicity F s + zeroMultiplicity G s := by
  obtain ⟨hF0,hG0⟩ := (pairedCompleted_ne_zero_iff 0).mp h0
  unfold zeroMultiplicity
  rw [pairedCompleted_meromorphicOrderAt hF hG s]
  exact WithTop.untop₀_add (entire_order_ne_top hF hF0 s) (entire_order_ne_top hG hG0 s)

end
end ArtinMatthews.VaryingKummerAnalytic
