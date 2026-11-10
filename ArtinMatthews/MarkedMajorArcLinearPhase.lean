module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
public import ArtinMatthews.MarkedSparsePhaseKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseSecondDerivative
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseUniform
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform logarithmic-phase cancellation with an arbitrary additive twist.
The near range uses the genuine second-derivative estimate, and the far
range the proved bounded-order differencing estimate. The near saving is
`|t|⁻¹ᐟ²`, which suffices for arbitrary logarithmic cancellation. -/
namespace ArtinMatthews

open Finset Filter OAI.JointDickman OAI.Problem337
open scoped Topology

lemma marked_linear_log_phase_second {U Z : ℝ} (hU : 1 ≤ U) (hZ : Z ≠ 0)
    (a : ℝ) (L R : ℕ) (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) :
    ‖∑ n ∈ Icc L R, ExponentialSum.phase (a*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤
      1000*(Real.sqrt |Z|+U/Real.sqrt |Z|) := by
  have hU0 : 0 < U := by linarith
  have hZ0 : 0 < |Z| := abs_pos.mpr hZ
  by_cases hLR : L ≤ R
  · let N := R+1-L
    have hN : (L:ℝ)+(N:ℝ)=(R:ℝ)+1 := by
      exact_mod_cast (show L+N=R+1 by dsimp [N]; omega)
    have hNle : (N:ℝ) ≤ 2*U := by linarith
    have hh := logarithmic_difference_sum_bound [] (by simp) a Z U L N hZ hU0 hL
      (by simp only [List.sum_nil,add_zero]; linarith)
    simp only [List.prod_nil,List.length_nil,zero_add,Nat.factorial_one,
      Nat.cast_one,one_mul,forwardDifference] at hh
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hh
    have hs : Real.sqrt (|Z|/(4*U)^2)=Real.sqrt |Z|/(4*U) := by
      rw [Real.sqrt_div (abs_nonneg _),Real.sqrt_sq (by positivity)]
    rw [hs] at hh
    have hsqrt : 0 < Real.sqrt |Z| := Real.sqrt_pos.mpr hZ0
    have hn : (N:ℝ)*(Real.sqrt |Z|/(4*U)) ≤ Real.sqrt |Z| := by
      calc
        _ = ((N:ℝ)/(4*U))*Real.sqrt |Z| := by ring
        _ ≤ 1*Real.sqrt |Z| := mul_le_mul_of_nonneg_right
          ((div_le_one (by positivity)).mpr (by linarith)) (Real.sqrt_nonneg |Z|)
        _ = _ := one_mul _
    have hi : 1/(Real.sqrt |Z|/(4*U))=4*(U/Real.sqrt |Z|) := by field_simp
    rw [hi] at hh
    have hset : Icc L R=Ico L (R+1) := by ext n; simp
    rw [hset,sum_Ico_eq_sum_range]
    have he : (∑ k ∈ range (R+1-L),
        ExponentialSum.phase (a*((L+k:ℕ):ℝ)+Z*Real.log ((L+k:ℕ):ℝ))) =
        ∑ j ∈ range N, ExponentialSum.phase (a*((j:ℝ)+(L:ℝ))+Z*Real.log ((j:ℝ)+(L:ℝ))) := by
      apply sum_congr rfl
      intro j hj
      simp only [Nat.cast_add,add_comm]
    rw [he]
    apply hh.trans
    have hp : 0 ≤ U/Real.sqrt |Z| := by positivity
    nlinarith
  · rw [Icc_eq_empty (by omega),sum_empty,norm_zero]
    positivity

/-- Actual sharp sums with an arbitrary linear frequency have a uniform
reciprocal-square-root plus power-saving bound through any fixed power range. -/
theorem marked_linear_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (a Z : ℝ) (L R : ℕ),
        1 ≤ |Z| → |Z| ≤ U^B → U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, ExponentialSum.phase (a*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤
          A*(U/Real.sqrt |Z|+U^(1-δ)) := by
  obtain ⟨C,η,hC,hη,hbound⟩ := logarithmic_phase_uniform B hB
  let δ := min η (1/2:ℝ)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := min_le_right _ _
  refine ⟨max C 1000,δ,lt_of_lt_of_le hC (le_max_left _ _),hδ,hδhalf,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with U hU hU1
  intro a Z L R hZ1 hZ hL hR
  have hU0 : 0 < U := by linarith
  have hp : 0 ≤ U^(1-δ) := Real.rpow_nonneg hU0.le _
  have hfrac : 0 ≤ U/Real.sqrt |Z| := by positivity
  have hmaxC : C ≤ max C 1000 := le_max_left _ _
  have hmax1 : (1000:ℝ) ≤ max C 1000 := le_max_right _ _
  by_cases hlo : U^(1/2:ℝ) ≤ |Z|
  · have hraw := hU a Z (L:ℤ) (R:ℤ) hlo hZ
      (by simpa only [Int.cast_natCast] using hL)
      (by simpa only [Int.cast_natCast] using hR)
    have hsum : (∑ n ∈ Icc L R, ExponentialSum.phase (a*(n:ℝ)+Z*Real.log (n:ℝ))) =
        ∑ n ∈ Icc (L:ℤ) R, differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ)) := by
      simpa only [Int.cast_natCast,differencingPhase,ExponentialSum.phase] using
        marked_nat_int_interval_sum
          (fun n : ℤ => differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ))) L R
    rw [hsum]
    have hpow : U^(1-η) ≤ U^(1-δ) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
    calc
      _ ≤ C*U^(1-η) := hraw
      _ ≤ C*U^(1-δ) := mul_le_mul_of_nonneg_left hpow hC.le
      _ ≤ (max C 1000)*U^(1-δ) := mul_le_mul_of_nonneg_right hmaxC hp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hC.le.trans hmaxC)
  · have hZU : |Z| ≤ U := (le_of_not_ge hlo).trans
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hU1 (show (1/2:ℝ) ≤ 1 by norm_num))
    have hsqrt : Real.sqrt |Z| ≤ U^(1-δ) := by
      calc
        _ ≤ Real.sqrt U := Real.sqrt_le_sqrt hZU
        _ = U^(1/2:ℝ) := Real.sqrt_eq_rpow _
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
    have hZn : Z ≠ 0 := by intro he; norm_num [he] at hZ1
    exact (marked_linear_log_phase_second hU1 hZn a L R hL hR).trans
      ((mul_le_mul_of_nonneg_left (by linarith : Real.sqrt |Z|+U/Real.sqrt |Z| ≤
        U/Real.sqrt |Z|+U^(1-δ)) (by norm_num : (0:ℝ)≤1000)).trans
        (mul_le_mul_of_nonneg_right hmax1 (by positivity)))

end ArtinMatthews
