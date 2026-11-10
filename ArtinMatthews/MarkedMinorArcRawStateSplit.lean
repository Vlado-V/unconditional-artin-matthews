module

public import ArtinMatthews.MarkedMinorArcRawState
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

/-! Exact conditioning of the actual full raw state by the copied active
prefix and the unchanged indexed memory. The true factorial measure remains. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Split the actual full active lists into copied slots and the last label. -/
def markedRawActiveSplit {J : Type*} {P : J → Finset Nat.Primes} (pads : ℕ) :
    MarkedRawActive P (pads+1) ≃ (MarkedRawActive P pads × ((j : J) → ↥(P j))) where
  toFun a := (fun j k => a j k.castSucc,fun j => a j (Fin.last pads))
  invFun a j := Fin.snoc (a.1 j) (a.2 j)
  left_inv a := by funext j; exact Fin.snoc_init_self (a j)
  right_inv a := by ext j k <;> simp

/-- The last active labels have exactly their product prime measure. -/
noncomputable def markedRawLastMass {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (last : (j : J) → ↥(P j)) : ℝ := ∏ j, ν j (last j)

theorem markedRawActiveMass_split {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (pads : ℕ) (a : MarkedRawActive P (pads+1)) :
    markedRawActiveMass ν a=markedRawActiveMass ν ((markedRawActiveSplit pads) a).1 *
      markedRawLastMass ν ((markedRawActiveSplit pads) a).2 := by
  unfold markedRawActiveMass markedRawLastMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact Fin.prod_univ_castSucc (fun k => ν j (a j k))

abbrev MarkedRawBackground {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)
    (pads B : ℕ) := MarkedRawActive P pads × MarkedRawMemory P B

noncomputable def markedRawBackgroundMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {pads B : ℕ}
    (b : MarkedRawBackground P pads B) : ℝ := markedRawActiveMass ν b.1 * markedRawMemoryMass ν b.2

/-- This is the literal finite clean-edge conditioning, not an abstract
replacement of the source state: copied prefix and memory are unchanged. -/
def markedRawStateSplit {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (pads B : ℕ) (Z : Finset (ℤ × ℤ)) :
    MarkedRawState P (pads+1) B Z ≃
      (MarkedRawBackground P pads B × (Z × ((j : J) → ↥(P j)))) where
  toFun s := (((markedRawActiveSplit pads s.2.1).1,s.2.2),
    (s.1,(markedRawActiveSplit pads s.2.1).2))
  invFun s := (s.2.1,((markedRawActiveSplit pads).symm (s.1.1,s.2.2),s.1.2))
  left_inv s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2))=s
    rw [Equiv.symm_apply_apply]
  right_inv s := by
    rcases s with ⟨⟨copied,memory⟩,⟨z,last⟩⟩
    simp

theorem markedRawStateMass_split {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (pads B : ℕ) (Z : Finset (ℤ × ℤ))
    (s : MarkedRawState P (pads+1) B Z) :
    markedRawStateMass ν s=markedRawBackgroundMass ν ((markedRawStateSplit pads B Z) s).1 *
      markedRawLastMass ν ((markedRawStateSplit pads B Z) s).2.2 := by
  unfold markedRawStateMass markedRawBackgroundMass
  rw [markedRawActiveMass_split ν pads]
  dsimp [markedRawStateSplit]
  ring

/-- Conditioning by copied slots and pending memory preserves the exact
physical weighted L² energy, with no factor from the number of backgrounds. -/
theorem markedRawState_energy_split {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ s : MarkedRawState P (pads+1) B Z, markedRawStateMass ν s*‖f s‖^2) =
      ∑ b : MarkedRawBackground P pads B, markedRawBackgroundMass ν b *
        ∑ z : Z, ∑ last : (j : J) → ↥(P j), markedRawLastMass ν last *
          ‖f ((markedRawStateSplit pads B Z).symm (b,(z,last)))‖^2 := by
  classical
  rw [← Equiv.sum_comp (markedRawStateSplit pads B Z).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro last _
  rw [markedRawStateMass_split ν pads B Z]
  simp only [Equiv.apply_symm_apply]
  ring

end ArtinMatthews
