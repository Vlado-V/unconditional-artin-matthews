module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Fixed ghost constants are absorbed uniformly in every positive word
length. The choice of rho is explicit and satisfies the actual ghost gap. -/

noncomputable section
namespace ArtinMatthews
open Filter

def markedMemoryChosenRho (q : ℝ) : ℝ := Real.sqrt ((1+Real.sqrt q)/2)

theorem markedMemoryChosenRho_bounds {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    0 < markedMemoryChosenRho q ∧ markedMemoryChosenRho q < 1 ∧
      Real.sqrt q < (markedMemoryChosenRho q)^2 := by
  have hs₀ := Real.sqrt_nonneg q
  have hs₁ : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq₀]
  have hp : 0 < (1+Real.sqrt q)/2 := by positivity
  have he : (markedMemoryChosenRho q)^2 = (1+Real.sqrt q)/2 := Real.sq_sqrt hp.le
  have hr : 0 < markedMemoryChosenRho q := Real.sqrt_pos.2 hp
  refine ⟨hr, ?_, ?_⟩ <;> nlinarith

theorem markedMemory_word_constant_budget {C : ℝ} (hC : 1 ≤ C) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 0 < n →
      2*C^(n+1)*((Real.log x)^(-(G+2)))^n ≤ ((Real.log x)^(-G))^n := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*C^2)))] with x hx
  have hL₁ : 1 ≤ Real.log x := (le_max_left _ _).trans hx
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL₁
  have hCL : 2*C^2 ≤ (Real.log x)^2 := by
    have h := (le_max_right _ _).trans hx
    nlinarith
  intro n hn
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hε : 0 ≤ (Real.log x)^(-(G+2)) := Real.rpow_nonneg hL.le _
  have hcoeff : 2*C^(n+1) ≤ (2*C^2)^n := by
    have hn' : n+1 ≤ 2*n := by omega
    have hc := pow_le_pow_right₀ hC hn'
    have ht : (2:ℝ) ≤ 2^n := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    calc
      2*C^(n+1) ≤ 2^n*C^(2*n) := mul_le_mul ht hc (pow_nonneg hC₀ _) (by positivity)
      _ = (2*C^2)^n := by rw [mul_pow, pow_mul]
  have heq : (Real.log x)^2*(Real.log x)^(-(G+2)) = (Real.log x)^(-G) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ ≤ (2*C^2)^n*((Real.log x)^(-(G+2)))^n :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hε _)
    _ = (2*C^2*(Real.log x)^(-(G+2)))^n := (mul_pow _ _ _).symm
    _ ≤ ((Real.log x)^2*(Real.log x)^(-(G+2)))^n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCL hε) n
    _ = _ := by rw [heq]

end ArtinMatthews
