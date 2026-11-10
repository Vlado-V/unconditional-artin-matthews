module

public import ArtinMatthews.MarkedMemoryHistoryRunWeight
public import ArtinMatthews.MarkedMemoryIndependentCorrespondence
public import ArtinMatthews.MarkedMemoryIndependentCorrespondenceGroup
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

/-! Birth mass of an independent identity. Initial identities carry one
in the chronological weight; their nu factor belongs to the separate
initial-state measure. A positive odd first time is a ghost creation. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryTraceBirth_isGhost {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryHistoryBirthIsGhost hZ history (markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩) =
      decide (t % 2 = 0) := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => rfl
    | succ t => exact PEmpty.elim b
  | succ n ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        change markedMemoryHistoryBirthIsGhost hZ history.2.2
          (markedMemoryHistoryTraceBirthEquiv hZ history.2.2 ⟨t,b⟩) = decide ((t+2)%2=0)
        rw [ih history.2.2 t b]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega

omit [Fintype J] in
theorem markedMemoryBandPrime_eq {a b : Σ j, ↥(P j)}
    (hg : a.1 = b.1) (hp : a.2.1 = b.2.1) : a = b := by
  rcases a with ⟨j,a⟩
  rcases b with ⟨k,b⟩
  cases hg
  have h : a = b := Subtype.ext hp
  cases h
  rfl

variable [DecidableEq J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

def markedMemoryIndependentBandPrime (a : Σ j, A j) : Σ j, ↥(P j) :=
  ⟨a.1,(d.particle a.1 a.2).1⟩

omit [DecidableEq J] in
theorem markedMemoryIndependent_birth_bandPrime (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryHistoryBirthLabel hZ history (markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩) =
      markedMemoryIndependentBandPrime hZ d (markedMemoryIndependentAddressEquiv hZ d order (Sum.inr ⟨t,b⟩)) := by
  apply markedMemoryBandPrime_eq
  · exact (markedMemoryIndependentAddress_group hZ d order (Sum.inr ⟨t,b⟩)).symm
  · exact (markedMemoryHistoryBirthLabel_prime hZ history _).trans
      ((markedMemoryHistoryTraceBirthEquiv_prime hZ history ⟨t,b⟩).trans
        (markedMemoryIndependentAddress_prime hZ d order (Sum.inr ⟨t,b⟩)).symm)

def markedMemoryIndependentBirthMass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (a : Σ j, A j) : ℝ :=
  if (d.lifespan a.1).first a.2 = 0 then 1 else
    (if (d.lifespan a.1).first a.2 % 2 = 1 then V a.1 else 1) * ν a.1 (d.particle a.1 a.2).1

omit [DecidableEq J] in
theorem markedMemoryIndependent_birthMass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryTraceBirthMass ν V hZ history a =
      markedMemoryIndependentBirthMass hZ d ν V (markedMemoryIndependentAddressEquiv hZ d order a) := by
  cases a with
  | inl old =>
    unfold markedMemoryIndependentBirthMass
    rw [← markedMemoryIndependentAddress_birth]
    rfl
  | inr b =>
    rcases b with ⟨t,b⟩
    have hf := markedMemoryIndependentAddress_birth hZ d order (Sum.inr ⟨t,b⟩)
    change t+1 = _ at hf
    unfold markedMemoryIndependentBirthMass
    rw [← hf]
    rw [ite_eq_right (by omega : ¬ t+1 = 0)]
    unfold markedMemoryHistoryTraceBirthMass
    dsimp only [Sum.elim_inr]
    rw [markedMemoryTraceBirth_isGhost, markedMemoryIndependent_birth_bandPrime hZ d order t b]
    have hparity : t % 2 = 0 ↔ (t+1) % 2 = 1 := by omega
    simp only [decide_eq_true_eq, hparity]
    rfl

end
end ArtinMatthews
