module

public import ArtinMatthews.VaryingKummerAnalyticNearOneZeros
public import ArtinMatthews.VaryingKummerAnalyticZeroReflection
public import ArtinMatthews.VaryingKummerAnalyticPoleComparison
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Generic near-one and separated zero-pole sums, extracted from
OpenAI PrimePackets/ZeroSeparation.lean. -/
namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open ArtinMatthews.ReusedGrowth
namespace PrimeDegreePackets.AnalyticGrowth

lemma outside_nearOneBox_scaled_gap {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hbox : ¬ InNearOneBox L ρ) :
    (1/4:ℝ)^2 ≤ (L*(1-ρ.re))^2+(L*ρ.im)^2 := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  by_contra h
  have hsq : (L*(1-ρ.re))^2+(L*ρ.im)^2 < (1/4:ℝ)^2 := lt_of_not_ge h
  have hXq : L*(1-ρ.re) ≤ 1/4 := by nlinarith [sq_nonneg (L*ρ.im)]
  have hYq : |L*ρ.im| ≤ 1/4 := by
    have H := sq_abs (L*ρ.im)
    nlinarith [sq_nonneg (L*(1-ρ.re)), abs_nonneg (L*ρ.im)]
  apply hbox
  constructor
  · have H := (le_div_iff₀ hL).mpr (show (1-ρ.re)*L ≤ 1/4 by nlinarith only [hXq])
    have HE : (1/4:ℝ)/L = 1/(4*L) := by ring
    rw [HE] at H
    linarith
  · rw [abs_mul, abs_of_pos hL] at hYq
    have H := (le_div_iff₀ hL).mpr (show |ρ.im| * L ≤ 1/4 by nlinarith only [hYq])
    simpa only [div_div] using H

lemma realZeroPole_le_base_of_outside_box {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L) (ρ : ℂ)
    (hbox : ¬ InNearOneBox L ρ) :
    realZeroPole f (1+h) ρ ≤ 676*realZeroPole f (1+1/L) ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole,hm]
  have hβ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hU : 0 < L*h := mul_pos hL hh
  have hU4 : L*h ≤ 4 := by have H := (le_div_iff₀ hL).mp hh4; nlinarith only [H]
  have H := realPoleKernel_comparison (by norm_num : (0:ℝ)<1/4) hX hU hU4
    (outside_nearOneBox_scaled_gap hL hβ hbox)
  norm_num only at H
  have HL := mul_le_mul_of_nonneg_left H hL.le
  have HN := mul_le_mul_of_nonneg_left HL
    (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [realZeroPole, real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  unfold realPoleKernel at HN
  nlinarith only [HN]

 

def nearOneZeroPole (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) : ℝ :=
  if InNearOneBox L ρ then realZeroPole f s ρ else 0

def separatedZeroPole (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) : ℝ :=
  if InNearOneBox L ρ then 0 else realZeroPole f s ρ

lemma zeroPole_split (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) :
    nearOneZeroPole f L s ρ + separatedZeroPole f L s ρ = realZeroPole f s ρ := by
  unfold nearOneZeroPole separatedZeroPole
  split <;> simp

lemma nearOneZeroPole_summable {f : ℂ → ℂ} {L s : ℝ}
    (H : Summable (realZeroPole f s)) : Summable (nearOneZeroPole f L s) := by
  exact H.indicator {ρ | InNearOneBox L ρ}

lemma separatedZeroPole_summable {f : ℂ → ℂ} {L s : ℝ}
    (H : Summable (realZeroPole f s)) : Summable (separatedZeroPole f L s) := by
  have HE : separatedZeroPole f L s =
      fun ρ => realZeroPole f s ρ - nearOneZeroPole f L s ρ := by
    funext ρ
    have H := zeroPole_split f L s ρ
    linarith
  rw [HE]
  exact H.sub (nearOneZeroPole_summable H)

end PrimeDegreePackets.AnalyticGrowth

namespace PrimeDegreePackets.AnalyticGrowth

lemma nearOneZeroPole_sum_of_no_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {L s : ℝ}
    (H : ∀ ρ, f ρ = 0 → ¬ InNearOneBox L ρ) :
    (∑' ρ, nearOneZeroPole f L s ρ) = 0 := by
  have Hz (ρ : ℂ) : nearOneZeroPole f L s ρ = 0 := by
    unfold nearOneZeroPole
    split
    next hbox =>
      have hm : zeroMultiplicity f ρ = 0 :=
        (zeroMultiplicity_eq_zero_iff hf h0 ρ).mpr (fun hρ => H ρ hρ hbox)
      simp [realZeroPole,hm]
    · rfl
  simp [Hz]

lemma nearOneZeroPole_sum_of_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {L s : ℝ} {ρ : ℂ}
    (hbox : InNearOneBox L ρ) (hm : zeroMultiplicity f ρ = 1) (hreal : ρ.im = 0)
    (H : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ) :
    (∑' τ, nearOneZeroPole f L s τ) = 1/(s-ρ.re) := by
  have Hz (τ : ℂ) (hne : τ ≠ ρ) : nearOneZeroPole f L s τ = 0 := by
    unfold nearOneZeroPole
    split
    next hτ =>
      have hmult : zeroMultiplicity f τ = 0 :=
        (zeroMultiplicity_eq_zero_iff hf h0 τ).mpr (fun hz => hne (H τ hz hτ))
      simp [realZeroPole,hmult]
    · rfl
  rw [tsum_eq_single ρ Hz, nearOneZeroPole, ite_eq_left hbox, realZeroPole, hm]
  have HE : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hreal]
  rw [HE]
  norm_cast
  simp

end PrimeDegreePackets.AnalyticGrowth
end
end
end OAI
