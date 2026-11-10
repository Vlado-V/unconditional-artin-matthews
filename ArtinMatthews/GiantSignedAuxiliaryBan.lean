module

public import ArtinMatthews.GiantSignedAuxiliaryCollision
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

/-! The original free/active exclusion is equivalent to the coordinate
collision event under the actual disjoint prime groups. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantSignedAuxiliaryBan {J : Type*} {P : J → Finset ℕ} {k M : ℕ}
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M)
    (aux : GiantTwoSidedPatternAuxiliary P C) : Prop :=
  ∀ g j (i : C g) (l : Fin M),
    (aux g i).val ≠ (a j l).val ∧ (aux g i).val ≠ (b j l).val

theorem giantSignedAuxiliaryBan_iff
    {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M)
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    GiantSignedAuxiliaryBan C a b aux ↔
      ¬∃ e : (Σ g : J, C g) × (Bool × Fin M), giantSignedAuxCollisionEvent C a b e aux := by
  constructor
  · intro h
    rintro ⟨⟨⟨g, i⟩, side, l⟩, he⟩
    cases side
    · exact (h g g i l).1 (congrArg Subtype.val he)
    · exact (h g g i l).2 (congrArg Subtype.val he)
  · intro h g j i l
    by_cases hgj : g = j
    · subst j
      constructor
      · intro he
        apply h
        exact ⟨(⟨g, i⟩, false, l), Subtype.ext he⟩
      · intro he
        apply h
        exact ⟨(⟨g, i⟩, true, l), Subtype.ext he⟩
    · have hd := Finset.disjoint_left.mp (hdis hgj)
      constructor
      · intro he
        exact hd (aux g i).property (he.symm ▸ (a j l).property)
      · intro he
        exact hd (aux g i).property (he.symm ▸ (b j l).property)

theorem giantSignedAuxiliaryBan_probability
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M) (α : ℝ)
    (hAtom : ∀ j p, markedHarmonicAtom (P j) p ≤ α) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ)) ≤
      ((∑ g, (C g).card) * (2 * M) : ℕ) * α := by
  have he (aux : GiantTwoSidedPatternAuxiliary P C) :
      (if GiantSignedAuxiliaryBan C a b aux then (0 : ℝ) else 1) =
        if ∃ e : (Σ g : J, C g) × (Bool × Fin M), giantSignedAuxCollisionEvent C a b e aux then 1 else 0 := by
    rw [giantSignedAuxiliaryBan_iff hdis]
    split_ifs <;> simp_all
  simp_rw [he]
  have h := giantSignedAuxCollision_probability_le hV C a b α hAtom
  simpa only [giantSignedAuxCollision_index_card] using h

end
end ArtinMatthews
