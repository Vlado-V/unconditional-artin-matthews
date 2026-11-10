module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.MarkedMajorArcLinearPhase
public import ArtinMatthews.MarkedSparsePhaseKernel
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
public import OAI.NumberTheory.JointDickman.Analysis.CharacterFourierExpansion
public import OAI.NumberTheory.JointDickman.Analysis.CharacterLogPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Actual character-twisted integer phases, including the low logarithmic
frequency regime needed for the rough-number truncation. -/
namespace ArtinMatthews

open Finset Filter OAI.JointDickman OAI.Problem337
open scoped Topology

theorem marked_character_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (t : ℝ) (L R : ℕ),
        1 ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)‖ ≤
          (q:ℝ)*A*(U/Real.sqrt |t/(2*Real.pi)|+U^(1-δ)) := by
  obtain ⟨A,δ,hA,hδ,hδhalf,hbound⟩ := marked_linear_log_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,hδhalf,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro q _ χ t L R hlo hhi hL hR
  let Z := t/(2*Real.pi)
  have hnatInt (a : ℝ) :
      (∑ n ∈ Icc L R, ExponentialSum.phase (a*(n:ℝ)+Z*Real.log (n:ℝ))) =
      ∑ n ∈ Icc (L:ℤ) R, differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ)) := by
    simpa only [Int.cast_natCast,differencingPhase,ExponentialSum.phase] using
      marked_nat_int_interval_sum
        (fun n : ℤ => differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ))) L R
  have hlinear (a : ℝ) :
      ‖∑ n ∈ Icc (L:ℤ) R, differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤
        A*(U/Real.sqrt |Z|+U^(1-δ)) := by
    rw [← hnatInt]
    exact hbound a Z L R hlo hhi hL hR
  have hh := character_log_sum_bound χ (Icc (L:ℤ) R) Z
    (A*(U/Real.sqrt |Z|+U^(1-δ))) (by positivity) hlinear
  have he : (∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)) =
      ∑ n ∈ Icc (L:ℤ) R, χ (n:ZMod q)*differencingPhase (Z*Real.log (n:ℝ)) := by
    have hsum := marked_nat_int_interval_sum
      (fun n : ℤ => χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)) L R
    simp only [Int.cast_natCast] at hsum
    rw [hsum]
    apply sum_congr rfl
    intro n hn
    have hLn : (L:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnR : (0:ℝ) < n := hU.trans_le (hL.trans hLn)
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hp := imaginary_power_as_log_phase (-t) hn0
    simp only [Complex.ofReal_neg,neg_mul,neg_neg] at hp
    rw [hp]
  rw [he]
  simpa only [mul_assoc] using hh

end ArtinMatthews
