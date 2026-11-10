module

public import ArtinMatthews.MarkedMinorArcRawStateSplit
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite splitting of the original state measure into copied
active slots, position, last active slots and indexed pending memory. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawState_sum_last_fibers
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ s : MarkedRawState P (pads+1) B Z, (markedRawStateMass ν s : ℂ) * F s) =
      ∑ copied : MarkedRawActive P pads, (markedRawActiveMass ν copied : ℂ) *
        ∑ z : Z, ∑ a : (j : J) → ↥(P j), (markedRawLastMass ν a : ℂ) *
          ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) *
            F (z, ((markedRawActiveSplit pads).symm (copied,a),m)) := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ z : Z, ∑ ca : MarkedRawActive P pads × ((j : J) → ↥(P j)),
        ∑ m : MarkedRawMemory P B,
          (markedRawStateMass ν (z, ((markedRawActiveSplit pads).symm ca,m)) : ℂ) *
            F (z, ((markedRawActiveSplit pads).symm ca,m)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact ((markedRawActiveSplit (P := P) pads).symm.sum_comp
        (fun active => ∑ m : MarkedRawMemory P B,
          (markedRawStateMass ν (z,(active,m)) : ℂ) * F (z,(active,m)))).symm
    _ = ∑ z : Z, ∑ copied : MarkedRawActive P pads,
        (markedRawActiveMass ν copied : ℂ) *
          ∑ a : (j : J) → ↥(P j), (markedRawLastMass ν a : ℂ) *
            ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) *
              F (z, ((markedRawActiveSplit pads).symm (copied,a),m)) := by
      simp only [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro copied _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro m _
      unfold markedRawStateMass
      rw [markedRawActiveMass_split ν pads, Equiv.apply_symm_apply]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end
end ArtinMatthews
