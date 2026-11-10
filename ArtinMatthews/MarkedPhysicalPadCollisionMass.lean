module

public import ArtinMatthews.MarkedPhysicalPadCollisionFlags
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

/-! The actual product harmonic law of all ordered auxiliary pads.
Group marginals and the global collision union bound are derived from
finite sum/product distributivity, with the two unshared labels fixed
arbitrarily in their original bands. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (M : ℕ)

def markedPhysicalPadHarmonicMass (c : MarkedPhysicalMarking P M) : ℝ :=
  ∏ j, ∏ k, markedHarmonicAtom (P j) (c j k)

def MarkedPhysicalPadCollisionEvent (b a : (j : J) → ↥(P j))
    (c : MarkedPhysicalMarking P M) : Prop :=
  ∃ j, MarkedPadCollision {b j,a j} (c j)

def markedPhysicalPadCollisionMass (b a : (j : J) → ↥(P j)) : ℝ :=
  markedEventMass (markedPhysicalPadHarmonicMass P M) (MarkedPhysicalPadCollisionEvent P M b a)

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalPadUnion_distinct_iff_event
    (c : MarkedPhysicalMarking P M) (b a : (j : J) → ↥(P j)) :
    MarkedPhysicalMarkingDistinct (markedPhysicalPadUnion c b a) ↔
      ¬MarkedPhysicalPadCollisionEvent P M b a c ∧ ∀ j, b j ≠ a j := by
  rw [markedPhysicalPadUnion_distinct_iff]
  simp only [MarkedPhysicalPadCollisionEvent, not_exists]

omit [DecidableEq J] in
theorem markedPhysicalPadHarmonicMass_nonneg
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (c : MarkedPhysicalMarking P M) :
    0 ≤ markedPhysicalPadHarmonicMass P M c :=
  Finset.prod_nonneg (fun j _ => Finset.prod_nonneg
    (fun _ _ => markedHarmonicAtom_nonneg (P j) (hV j)))

theorem markedPhysicalPadHarmonicMass_sum
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ c : MarkedPhysicalMarking P M, markedPhysicalPadHarmonicMass P M c) = 1 := by
  simpa only [markedPhysicalMass_mul_reciprocal, markedPhysicalPadHarmonicMass] using
    markedPhysicalMarking_normalized_sum P M hV

theorem markedPhysicalPadCollisionMass_nonneg
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (b a : (j : J) → ↥(P j)) :
    0 ≤ markedPhysicalPadCollisionMass P M b a :=
  markedEventMass_nonneg _ (markedPhysicalPadHarmonicMass_nonneg P M hV) _

theorem markedPhysicalPadCollision_group_mass
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (b a : (j : J) → ↥(P j)) (j : J) :
    markedEventMass (markedPhysicalPadHarmonicMass P M)
        (fun c => MarkedPadCollision {b j,a j} (c j)) =
      markedEventMass (finiteProductMass (fun _ : Fin M => markedHarmonicAtom (P j)))
        (MarkedPadCollision {b j,a j}) := by
  classical
  let μ := fun j : J => fun c : Fin M → ↥(P j) =>
    ∏ k, markedHarmonicAtom (P j) (c k)
  let f := fun j : J => fun c : Fin M → ↥(P j) =>
    if MarkedPadCollision {b j,a j} c then (1:ℝ) else 0
  have hμ (j : J) : (∑ c : Fin M → ↥(P j), μ j c) = 1 := by
    dsimp only [μ]
    rw [← Fintype.prod_sum (fun (_k : Fin M) (p : ↥(P j)) => markedHarmonicAtom (P j) p)]
    simp_rw [markedHarmonicAtom_sum (P j) (hV j)]
    simp
  have h := finiteProduct_expectation_coordinate μ f hμ j
  simpa only [markedEventMass, markedPhysicalPadHarmonicMass, finiteProductMass, μ, f] using h

theorem markedPhysicalPadCollisionMass_union_le
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (b a : (j : J) → ↥(P j)) :
    markedPhysicalPadCollisionMass P M b a ≤
      ∑ j, markedEventMass (finiteProductMass (fun _ : Fin M => markedHarmonicAtom (P j)))
        (MarkedPadCollision {b j,a j}) := by
  have hu := markedEventMass_exists_le (markedPhysicalPadHarmonicMass P M)
    (markedPhysicalPadHarmonicMass_nonneg P M hV)
    (fun j c => MarkedPadCollision {b j,a j} (c j))
  change markedPhysicalPadCollisionMass P M b a ≤ _ at hu
  apply hu.trans_eq
  apply Finset.sum_congr rfl
  intro j _
  exact markedPhysicalPadCollision_group_mass P M hV b a j

theorem markedPhysicalPadCollisionMass_finite_bound
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (y : J → ℝ) (hy : ∀ j, 0 < y j)
    (hP : ∀ j p, p ∈ P j → y j ≤ (p:ℝ)) (b a : (j : J) → ↥(P j)) :
    markedPhysicalPadCollisionMass P M b a ≤
      ((M:ℝ)^2 + 2*(M:ℝ)) * ∑ j, 1/(y j * bandReciprocalMass (P j)) := by
  apply (markedPhysicalPadCollisionMass_union_le P M hV b a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hc : ({b j,a j}:Finset ↥(P j)).card ≤ 2 := by
    calc
      _ ≤ ({a j}:Finset ↥(P j)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hh := marked_harmonic_pad_collision_bound (P j) (hV j) (hy j) (hP j) M {b j,a j}
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr (mul_nonneg (hy j).le (hV j).le))
  have hc' : (({b j,a j}:Finset ↥(P j)).card:ℝ) ≤ 2 := by exact_mod_cast hc
  calc
    _ ≤ (M:ℝ)^2 + (M:ℝ)*2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg M))
    _ = _ := by ring

end
end ArtinMatthews
