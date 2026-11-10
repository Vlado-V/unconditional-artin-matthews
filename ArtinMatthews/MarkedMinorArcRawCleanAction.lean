module

public import ArtinMatthews.MarkedMinorArcRawStateSplit
public import ArtinMatthews.MarkedMinorArcWeightedConjugation
public import Mathlib.CategoryTheory.Category.Basic
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

/-! Exact no-store/no-promote raw row operation. The copied active slots and
all indexed pending particles are retained; each new last label has its
literal prime measure. This is a state identification, not a norm premise. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators

abbrev MarkedRawCleanFiber {J : Type*} (P : J → Finset Nat.Primes) (Z : Finset (ℤ × ℤ)) :=
  Z × ((j : J) → ↥(P j))

/-- The actual clean row-choice sum, with arbitrary literal geometric and
endpoint kernelK. It draws exactly one new prime per group and no memory. -/
noncomputable def markedRawCleanApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  let copied := (markedRawActiveSplit pads s.2.1).1
  let oldLast := (markedRawActiveSplit pads s.2.1).2
  ∑ z : Z, ∑ fresh : (j : J) → ↥(P j), (markedRawLastMass ν fresh : ℂ) *
    K (copied,s.2.2) (s.1,oldLast) (z,fresh) *
      f (z,((markedRawActiveSplit pads).symm (copied,fresh),s.2.2))

/-- Conditioning is an exact equality of actual row operations, retaining
all coefficients and the correct source/target measure convention. -/
theorem markedRawCleanApply_conditioned {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (b : MarkedRawBackground P pads B) (u : MarkedRawCleanFiber P Z) :
    markedRawCleanApply ν K f ((markedRawStateSplit pads B Z).symm (b,u)) =
      markedWeightedMatrixApply (fun t : MarkedRawCleanFiber P Z => markedRawLastMass ν t.2)
        (K b) (fun v => f ((markedRawStateSplit pads B Z).symm (b,v))) u := by
  rcases b with ⟨copied,memory⟩
  rcases u with ⟨z,oldLast⟩
  have heactive : markedRawActiveSplit pads
      (((markedRawStateSplit pads B Z).symm ((copied,memory),(z,oldLast))).2.1) = (copied,oldLast) := by
    change (markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm (copied,oldLast)) = _
    exact Equiv.apply_symm_apply _ _
  unfold markedRawCleanApply markedWeightedMatrixApply
  rw [heactive]
  change (∑ z' : Z, ∑ fresh : (j : J) → ↥(P j), (markedRawLastMass ν fresh : ℂ) *
      K (copied,memory) (z,oldLast) (z',fresh) *
      f ((markedRawStateSplit pads B Z).symm ((copied,memory),(z',fresh)))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z' _
  apply Finset.sum_congr rfl
  intro fresh _
  ring

/-- The genuine raw clean weighted energy is exactly the sum of the genuine
conditioned fiber energies, with the actual factorial background measure. -/
theorem markedRawCleanApply_energy_conditioned {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ s : MarkedRawState P (pads+1) B Z, markedRawStateMass ν s * ‖markedRawCleanApply ν K f s‖^2) =
      ∑ b : MarkedRawBackground P pads B, markedRawBackgroundMass ν b *
        ∑ z : Z, ∑ last : (j : J) → ↥(P j), markedRawLastMass ν last *
          ‖markedWeightedMatrixApply (fun t : MarkedRawCleanFiber P Z => markedRawLastMass ν t.2)
            (K b) (fun v => f ((markedRawStateSplit pads B Z).symm (b,v))) (z,last)‖^2 := by
  rw [markedRawState_energy_split ν pads B Z]
  simp only [markedRawCleanApply_conditioned]

end ArtinMatthews
