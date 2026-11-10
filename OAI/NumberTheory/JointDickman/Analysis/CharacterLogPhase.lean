module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import OAI.NumberTheory.EgyptianFractions.CorrelationPhase
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
public import OAI.NumberTheory.JointDickman.Analysis.CharacterFourierExpansion
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseUniform


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! # Character twists of logarithmic exponential sums -/
namespace JointDickman
open Complex Filter Problem337
open scoped Topology

lemma imaginary_power_as_log_phase (t : ℝ) {n : ℤ} (hn : 0 < n) :
    (n:ℂ)^(-((t:ℂ)*I)) =
      differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnC]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,←Complex.ofReal_log hn0.le]
  unfold differencingPhase
  congr 1
  push_cast
  field_simp

/-- A character contributes at most the finite Fourier expansion factor q.
The power saving is uniform in the character. -/
theorem character_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (t : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))‖ ≤
          (q:ℝ)*A*U^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := logarithmic_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro q _ χ t L R hlo hhi hL hR
  have he : (∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) =
      ∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*
        differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hLn : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0:ℝ) < n := hU.trans_le (hL.trans hLn)
    rw [imaginary_power_as_log_phase t (by exact_mod_cast hn0)]
  rw [he]
  have hh := character_log_sum_bound χ (Finset.Icc L R) (-t/(2*Real.pi))
    (A*U^(1-δ)) (by positivity) (fun a => hbound a (-t/(2*Real.pi)) L R
      (by simpa only [neg_div,abs_neg] using hlo)
      (by simpa only [neg_div,abs_neg] using hhi) hL hR)
  simpa only [mul_assoc] using hh

end JointDickman

end OAI
