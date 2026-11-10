module

public import ArtinMatthews.MarkedPhysicalMarking
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

/-! The literal primitive physical states with ordered full lists. Their
transport to typed raw slots preserves every label address and the original
physical mass. The raw-memory tilt is not asserted to preserve that mass. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def MarkedPhysicalStateCondition {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (z : ℤ × ℤ) (a : MarkedPhysicalMarking P M) : Prop :=
  IsCoprime z.1 z.2 ∧ MarkedPhysicalMarkingDistinct a ∧
    ∀ j k, ((a j k : ℕ) : ℤ) ∣ z.1

abbrev MarkedPhysicalState {J : Type*} (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :=
  {s : Z × MarkedPhysicalMarking P M // MarkedPhysicalStateCondition s.1.1 s.2}

def MarkedPhysicalArrayCondition {J : Type*} (z : ℤ × ℤ) {M : ℕ}
    (a : J → Fin M → ℕ) : Prop :=
  IsCoprime z.1 z.2 ∧ (∀ j, Function.Injective (a j)) ∧ ∀ j k, (a j k : ℤ) ∣ z.1

abbrev MarkedPhysicalArrayState {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :=
  {s : Z × ↥(representedArrayChoices P (fun _ => M)) //
    MarkedPhysicalArrayCondition s.1.1 s.2.1}

theorem markedPhysicalArrayCondition_iff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (z : ℤ × ℤ) (a : MarkedPhysicalMarking P M) :
    MarkedPhysicalArrayCondition z (markedPhysicalMarkingArrayEquiv P M a).1 ↔
      MarkedPhysicalStateCondition z a := by
  constructor
  · rintro ⟨hz, hi, hd⟩
    exact ⟨hz, fun j k l hkl => hi j (congrArg Subtype.val hkl), hd⟩
  · rintro ⟨hz, hi, hd⟩
    exact ⟨hz, fun j k l hkl => hi j (Subtype.ext hkl), hd⟩

/-- The selected marking arrays and the physical states are in bijection,
including their ordered-list multiplicities and their literal divisibility
and primitive-position tests. -/
def markedPhysicalStateArrayEquiv {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    MarkedPhysicalState P M Z ≃ MarkedPhysicalArrayState P M Z where
  toFun s := ⟨(s.1.1, markedPhysicalMarkingArrayEquiv P M s.1.2),
    (markedPhysicalArrayCondition_iff P M _ _).mpr s.2⟩
  invFun s := ⟨(s.1.1, (markedPhysicalMarkingArrayEquiv P M).symm s.1.2),
    (markedPhysicalArrayCondition_iff P M _ _).mp (by
      simpa only [Equiv.apply_symm_apply] using s.2)⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

/-- Exact transport of any original array summand; the state measure is
the original `∏ Vᵢ⁻ᴹ`, with no quotient by list permutations. -/
theorem markedPhysicalStateArray_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ)
    (F : MarkedPhysicalArrayState P M Z → ℂ) :
    (∑ s : MarkedPhysicalState P M Z,
      (markedPhysicalMass V M : ℂ) * F (markedPhysicalStateArrayEquiv P M Z s)) =
      ∑ s : MarkedPhysicalArrayState P M Z, (markedPhysicalMass V M : ℂ) * F s :=
  Equiv.sum_comp (markedPhysicalStateArrayEquiv P M Z)
    (fun s => (markedPhysicalMass V M : ℂ) * F s)

def markedPhysicalEmptyMemory {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) : MarkedRawMemory P 0 :=
  ⟨⟨fun _ => 0, by simp⟩, fun _ k => Fin.elim0 k⟩

theorem markedPhysicalEmptyMemory_mass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) :
    markedRawMemoryMass ν (markedPhysicalEmptyMemory P) = 1 := by
  simp only [markedRawMemoryMass, markedPhysicalEmptyMemory, Fin.val_zero,
    Nat.factorial_zero, Nat.cast_one, div_one]
  apply Finset.prod_eq_one
  intro j _
  apply Finset.prod_eq_one
  intro k _
  exact Fin.elim0 k

def markedPhysicalStateToRaw {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (s : MarkedPhysicalState P M Z) :
    MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z :=
  (s.1.1, (markedPhysicalMarkingEquiv P hP M).symm s.1.2,
    markedPhysicalEmptyMemory (fun j => markedRawPrimeBand (P j)))

theorem markedPhysicalStateToRaw_injective {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) : Function.Injective (markedPhysicalStateToRaw P hP M Z) := by
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun u : MarkedRawState (fun j => markedRawPrimeBand (P j)) M 0 Z => u.1) h
  · apply (markedPhysicalMarkingEquiv P hP M).symm.injective
    exact congrArg (fun u => u.2.1) h

theorem markedPhysicalStateToRaw_distinct {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (s : MarkedPhysicalState P M Z) :
    MarkedRawActiveDistinct (markedPhysicalStateToRaw P hP M Z s).2.1 := by
  apply (markedPhysicalMarkingEquiv_distinct P hP M _).mp
  simpa only [markedPhysicalStateToRaw, Equiv.apply_symm_apply] using s.2.2.1

/-- The boundary has empty pending memory and the original constant prime
atom `Vᵢ⁻¹`. This identifies its exact physical mass; the later tilted atom
requires the separate signed-memory identity. -/
theorem markedPhysicalStateToRaw_mass {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (s : MarkedPhysicalState P M Z) :
    markedRawStateMass (fun j _ => (V j)⁻¹) (markedPhysicalStateToRaw P hP M Z s) =
      markedPhysicalMass V M := by
  rw [markedRawStateMass, markedPhysicalStateToRaw, markedPhysicalEmptyMemory_mass, mul_one]
  exact (markedPhysicalMass_eq_rawActiveMass _ V M _).symm

/-- The source/target joint measure is exactly symmetric, as in PD03:
one original full-list mass and one new-slot atom per group. -/
theorem markedPhysicalMass_edge {J : Type*} [Fintype J] (V : J → ℝ) (M : ℕ) :
    markedPhysicalMass V M * (∏ j, (V j)⁻¹) = markedPhysicalMass V (M+1) := by
  simp only [markedPhysicalMass, ← Finset.prod_mul_distrib, pow_succ]

end ArtinMatthews
