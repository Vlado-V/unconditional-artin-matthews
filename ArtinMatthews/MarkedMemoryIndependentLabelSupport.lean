module

public import ArtinMatthews.MarkedMemoryIndependentGhostLabels
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The direct local identity functions are injected and have exactly
the prescribed interval support. These facts are transported from the
independently constructed active/pending population, not postulated. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependentVertexValue_injective (v : ℕ) (hv : v ≤ n) :
    Function.Injective (markedMemoryIndependentVertexValue hZ d v hv) := by
  intro x y hxy
  apply (markedMemoryPopulationStateCast (markedMemoryIndependentStageState_even hZ d v hv).symm).injective
  apply (markedMemoryIndependentPopulationLabel hZ d (2*v) (by omega)).injective
  exact (markedMemoryIndependentVertexValue_stage hZ d v hv x).trans
    (hxy.trans (markedMemoryIndependentVertexValue_stage hZ d v hv y).symm)

theorem markedMemoryIndependentPostGhostValue_injective (v : ℕ) (hv : v ≤ n) :
    Function.Injective (markedMemoryIndependentPostGhostValue hZ d v hv) := by
  intro x y hxy
  apply (markedMemoryPopulationStateCast (markedMemoryIndependentStageState_odd hZ d v hv).symm).injective
  apply (markedMemoryIndependentPopulationLabel hZ d (2*v+1) (by omega)).injective
  exact (markedMemoryIndependentPostGhostValue_stage hZ d v hv x).trans
    (hxy.trans (markedMemoryIndependentPostGhostValue_stage hZ d v hv y).symm)

def markedMemoryIndependentVertexIds (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryPopulationIndex (markedMemoryIndependentState hZ d v hv) ↪ Σ j, A j :=
  ⟨markedMemoryIndependentVertexValue hZ d v hv,markedMemoryIndependentVertexValue_injective hZ d v hv⟩

def markedMemoryIndependentPostGhostIds (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryPopulationIndex (markedMemoryIndependentPostGhost hZ d v hv) ↪ Σ j, A j :=
  ⟨markedMemoryIndependentPostGhostValue hZ d v hv,markedMemoryIndependentPostGhostValue_injective hZ d v hv⟩

theorem markedMemoryIndependentVertexIds_range (v : ℕ) (hv : v ≤ n) (a : Σ j, A j) :
    (∃ i, markedMemoryIndependentVertexIds hZ d v hv i = a) ↔
      (d.lifespan a.1).first a.2 ≤ 2*v ∧ 2*v ≤ (d.lifespan a.1).last a.2 := by
  let e := markedMemoryPopulationStateCast (markedMemoryIndependentStageState_even hZ d v hv).symm
  constructor
  · rintro ⟨i,hi⟩
    apply (markedMemoryIndependentPopulationLabel_range hZ d (2*v) (by omega) a).mp
    exact ⟨e i,(markedMemoryIndependentVertexValue_stage hZ d v hv i).trans hi⟩
  · intro ha
    obtain ⟨i,hi⟩ := (markedMemoryIndependentPopulationLabel_range hZ d (2*v) (by omega) a).mpr ha
    refine ⟨e.symm i,?_⟩
    exact (markedMemoryIndependentVertexValue_stage hZ d v hv (e.symm i)).symm.trans
      ((congrArg (markedMemoryIndependentPopulationLabel hZ d (2*v) (by omega))
        (e.apply_symm_apply i)).trans hi)

theorem markedMemoryIndependentPostGhostIds_range (v : ℕ) (hv : v ≤ n) (a : Σ j, A j) :
    (∃ i, markedMemoryIndependentPostGhostIds hZ d v hv i = a) ↔
      (d.lifespan a.1).first a.2 ≤ 2*v+1 ∧ 2*v+1 ≤ (d.lifespan a.1).last a.2 := by
  let e := markedMemoryPopulationStateCast (markedMemoryIndependentStageState_odd hZ d v hv).symm
  constructor
  · rintro ⟨i,hi⟩
    apply (markedMemoryIndependentPopulationLabel_range hZ d (2*v+1) (by omega) a).mp
    exact ⟨e i,(markedMemoryIndependentPostGhostValue_stage hZ d v hv i).trans hi⟩
  · intro ha
    obtain ⟨i,hi⟩ := (markedMemoryIndependentPopulationLabel_range hZ d (2*v+1) (by omega) a).mpr ha
    refine ⟨e.symm i,?_⟩
    exact (markedMemoryIndependentPostGhostValue_stage hZ d v hv (e.symm i)).symm.trans
      ((congrArg (markedMemoryIndependentPopulationLabel hZ d (2*v+1) (by omega))
        (e.apply_symm_apply i)).trans hi)

theorem markedMemoryIndependentVertexIds_first_zero
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))) :
    (d.lifespan (markedMemoryIndependentVertexIds hZ d 0 (Nat.zero_le n) i).1).first
      (markedMemoryIndependentVertexIds hZ d 0 (Nat.zero_le n) i).2 = 0 := by
  have h := (markedMemoryIndependentVertexIds_range hZ d 0 (Nat.zero_le n) _).mp ⟨i,rfl⟩
  omega

end
end ArtinMatthews
