module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Field.Basic
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Norm Subgroup -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup.Construction

noncomputable section

/-! The nonzero sums of two squares form an open subgroup containing all squares. -/

open Set Filter
open scoped _root_.Topology

def quadraticNormSubgroup (k : Type*) [Field k] : Subgroup kˣ where
  carrier := {a | ∃ x y : k, x ^ 2 + y ^ 2 = a.val}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, y, hx⟩ ⟨u, v, hu⟩
    refine ⟨x * u - y * v, x * v + y * u, ?_⟩
    change _ = a.val * b.val
    rw [← hx, ← hu]
    ring
  inv_mem' := by
    rintro a ⟨x, y, hx⟩
    refine ⟨x / a.val, y / a.val, ?_⟩
    rw [Units.val_inv_eq_inv_val]
    rw [div_pow, div_pow, ← add_div, hx]
    field_simp

theorem square_mem_quadraticNormSubgroup {k : Type*} [Field k] (a : kˣ) :
    a ^ 2 ∈ quadraticNormSubgroup k := ⟨a.val, 0, by simp⟩

def squareUnitsSubgroup (k : Type*) [CommGroup k] : Subgroup k :=
  (powMonoidHom 2 : k →* k).range

theorem squareUnitsSubgroup_le_quadraticNormSubgroup {k : Type*} [Field k] :
    squareUnitsSubgroup kˣ ≤ quadraticNormSubgroup k := by
  rintro a ⟨b, rfl⟩
  exact square_mem_quadraticNormSubgroup b

theorem mem_squareUnitsSubgroup_iff {k : Type*} [Field k] (a : kˣ) :
    a ∈ squareUnitsSubgroup kˣ ↔ ∃ x : k, x ^ 2 = a.val := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.val, congrArg Units.val hb⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro he
      exact a.ne_zero (by simpa [he] using hx.symm)
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply Units.ext
    exact hx

theorem squareUnitsSubgroup_isOpen
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    IsOpen (squareUnitsSubgroup kˣ : Set kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : kˣ))
  have h := (Units.continuous_val.continuousAt (x := (1 : kˣ))).preimage_mem_nhds
    (QuadraticNormAt.Construction.square_range_mem_nhds_one (k := k))
  apply Filter.mem_of_superset h
  intro a ha
  exact (mem_squareUnitsSubgroup_iff a).mpr ha

theorem quadraticNormSubgroup_isOpen
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    IsOpen (quadraticNormSubgroup k : Set kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : kˣ))
  exact Filter.mem_of_superset
    (squareUnitsSubgroup_isOpen.mem_nhds (Subgroup.one_mem _))
    squareUnitsSubgroup_le_quadraticNormSubgroup

theorem localField_quadraticNormSubgroup_isOpen
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (hnd : ¬ DiscreteTopology k) : IsOpen (quadraticNormSubgroup k : Set kˣ) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  · exact quadraticNormSubgroup_isOpen

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup.Construction
