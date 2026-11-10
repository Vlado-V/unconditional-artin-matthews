module

public import ArtinMatthews.GiantTwoSidedLabelOffsets
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

/-! Fixed label data separate the arithmetic root from every physical
marking. Reconstruction retains the exact slice tests and all original
copy and auxiliary-ban conditions. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

structure GiantTwoSidedLabelCompatible {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (s t : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P C) : Prop where
  copied : ∀ j (i : Fin k),i∉C j → t j (Fin.castAdd ell i)=s j (Fin.castAdd ell i)
  banned : ∀ g j (i : ↥(C g)) (l : Fin (k+ell)),
    (aux g i:ℕ) ≠ (s j l:ℕ) ∧ (aux g i:ℕ) ≠ (t j l:ℕ)

structure GiantTwoSidedPhysicalPathCondition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (I Z : Finset ℕ) (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z) : Prop where
  root_mem : (s 0).val.1.val∈I
  edges : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
    (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
    (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)

abbrev GiantTwoSidedPhysicalPath {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ) :=
  {s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z //
    GiantTwoSidedPhysicalPathCondition C π τ aux step I Z s}

abbrev GiantTwoSidedRootLabelData {J : Type*} {P : J → Finset ℕ} (k ell n : ℕ) (I : Finset ℕ) :=
  ↥I × (Fin (n+1) → MarkedPhysicalMarking P (k+ell))

def giantTwoSidedRootLabelPosition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) {I : Finset ℕ}
    (d : GiantTwoSidedRootLabelData (P:=P) k ell n I) (v : Fin (n+1)) : ℤ :=
  (d.1.val:ℤ)+giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.2 π aux step) v

structure GiantTwoSidedRootLabelCondition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    {I : Finset ℕ} (Z : Finset ℕ) (d : GiantTwoSidedRootLabelData (P:=P) k ell n I) : Prop where
  distinct : ∀ v,MarkedPhysicalMarkingDistinct (d.2 v)
  compatible : ∀ i,GiantTwoSidedLabelCompatible (C i)
    (giantTwoSidedPermuteLabels (π i) (d.2 i.castSucc))
    (giantTwoSidedPermuteLabels (τ i) (d.2 i.succ)) (aux i)
  nonneg : ∀ v,0≤giantTwoSidedRootLabelPosition C π aux step d v
  mem_slice : ∀ v,(giantTwoSidedRootLabelPosition C π aux step d v).toNat∈Z
  divides : ∀ v j l,(d.2 v j l:ℤ)∣giantTwoSidedRootLabelPosition C π aux step d v

abbrev GiantTwoSidedRootLabelPath {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ) :=
  {d : GiantTwoSidedRootLabelData (P:=P) k ell n I // GiantTwoSidedRootLabelCondition C π τ aux step Z d}

def giantTwoSidedRootLabel_reconstruct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) (v : Fin (n+1)) :
    GiantTwoSidedEndpointState P (k+ell) Z := by
  let z := giantTwoSidedRootLabelPosition C π aux step d.val v
  refine ⟨(⟨z.toNat,d.property.mem_slice v⟩,d.val.2 v),d.property.distinct v,?_⟩
  intro j l
  apply Int.natCast_dvd_natCast.mp
  rw [Int.toNat_of_nonneg (d.property.nonneg v)]
  exact d.property.divides v j l

theorem giantTwoSidedRootLabel_reconstruct_position {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) (v : Fin (n+1)) :
    ((giantTwoSidedRootLabel_reconstruct d v).val.1.val:ℤ)=
      giantTwoSidedRootLabelPosition C π aux step d.val v :=
  Int.toNat_of_nonneg (d.property.nonneg v)

theorem giantTwoSidedRootLabel_reconstruct_labels {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) (v : Fin (n+1)) :
    (giantTwoSidedRootLabel_reconstruct d v).val.2=d.val.2 v := rfl

theorem giantTwoSidedRootLabel_reconstruct_condition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) :
    GiantTwoSidedPhysicalPathCondition C π τ aux step I Z (giantTwoSidedRootLabel_reconstruct d) := by
  constructor
  · have hp := giantTwoSidedRootLabel_reconstruct_position d 0
    simp only [giantTwoSidedRootLabelPosition,giantTwoSidedPathOffset_zero,add_zero] at hp
    rw [Int.ofNat.inj hp]
    exact d.val.1.property
  · intro i
    refine ⟨(d.property.compatible i).copied,?_,(d.property.compatible i).banned⟩
    change ((giantTwoSidedRootLabel_reconstruct d i.succ).val.1.val:ℤ)=
      ((giantTwoSidedRootLabel_reconstruct d i.castSucc).val.1.val:ℤ)+_
    rw [giantTwoSidedRootLabel_reconstruct_position,giantTwoSidedRootLabel_reconstruct_position]
    unfold giantTwoSidedRootLabelPosition
    rw [giantTwoSidedPathOffset_succ]
    change (d.val.1.val:ℤ)+(_+giantTwoSidedLabelIncrement C d.val.2 π aux step i)=
      ((d.val.1.val:ℤ)+_)+giantTwoSidedLabelIncrement C d.val.2 π aux step i
    exact (add_assoc _ _ _).symm

end
end ArtinMatthews
