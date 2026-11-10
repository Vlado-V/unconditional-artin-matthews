module

public import ArtinMatthews.GiantSignedEdgeStorePromote
public import ArtinMatthews.MarkedBirthDistinctPermutation
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

/-! Births of the all-degree signed evolution. A copied or promoted label
is not a birth. Ordered ghost batches have their actual finite lengths. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} {P : B → Finset ℕ} {k ell n : ℕ}

abbrev GiantSignedBirthAddress (B : Type*) {k n : ℕ} (ell : ℕ)
    (C : Fin n → B → Finset (Fin k)) (batch : Fin (n+1) → B → ℕ) :=
  (B × Fin (k+ell)) ⊕
    ((Σ i : Fin n, Σ g : B, Fin (ell + (C i g).card)) ⊕
      (Σ i : Fin (n+1), Σ g : B, Fin (batch i g)))

inductive GiantSignedBirthOperation (n : ℕ)
  | initial
  | edge (i : Fin n)
  | visit (i : Fin (n+1))
  deriving DecidableEq, Fintype

def giantSignedBirthOperation (ell : ℕ) (C : Fin n → B → Finset (Fin k))
    (batch : Fin (n+1) → B → ℕ) :
    GiantSignedBirthAddress B ell C batch → GiantSignedBirthOperation n
  | .inl _ => .initial
  | .inr (.inl a) => .edge a.1
  | .inr (.inr a) => .visit a.1

structure GiantSignedBirthData (P : B → Finset ℕ) {k n : ℕ} (ell : ℕ)
    (C : Fin n → B → Finset (Fin k)) (batch : Fin (n+1) → B → ℕ) where
  initial : MarkedPhysicalMarking P (k+ell)
  target : Fin n → MarkedPhysicalMarking P (k+ell)
  promoted : (i : Fin n) → (g : B) → Finset (Fin (ell + (C i g).card))
  born : (i : Fin (n+1)) → (g : B) → Fin (batch i g) → P g

def giantSignedBirthValue {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch) :
    GiantSignedBirthAddress B ell C batch → Option ℕ
  | .inl a => some (d.initial a.1 a.2).val
  | .inr (.inl a) =>
      if a.2.2 ∈ d.promoted a.1 a.2.1 then none
      else some (giantSignedPatternFreeLabels (C a.1) (d.target a.1) a.2.1 a.2.2).val
  | .inr (.inr a) => some (d.born a.1 a.2.1 a.2.2).val

abbrev GiantSignedPerformedBirth {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch) :=
  (B × Fin (k+ell)) ⊕
    ((Σ i : Fin n, Σ g : B,
      {s : Fin (ell + (C i g).card) // s ∉ d.promoted i g}) ⊕
      (Σ i : Fin (n+1), Σ g : B, Fin (batch i g)))

def giantSignedPerformedBirthAddress {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch) :
    GiantSignedPerformedBirth d → GiantSignedBirthAddress B ell C batch :=
  Sum.map id (Sum.map (Sigma.map id (fun _ => Sigma.map id (fun _ a => a.val))) id)

def giantSignedPerformedBirthPrime {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch) :
    GiantSignedPerformedBirth d → ℕ
  | .inl a => (d.initial a.1 a.2).val
  | .inr (.inl a) =>
      (giantSignedPatternFreeLabels (C a.1) (d.target a.1) a.2.1 a.2.2.val).val
  | .inr (.inr a) => (d.born a.1 a.2.1 a.2.2).val

def GiantSignedBirthDistinct {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch) : Prop :=
  Function.Injective (giantSignedPerformedBirthPrime d)

theorem giantSignedPerformedBirthAddress_injective
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (d : GiantSignedBirthData P ell C batch) :
    Function.Injective (giantSignedPerformedBirthAddress d) := by
  apply Sum.map_injective.mpr
  refine ⟨Function.injective_id, ?_⟩
  apply Sum.map_injective.mpr
  refine ⟨?_, Function.injective_id⟩
  exact Function.injective_id.sigma_map (fun _ =>
    Function.injective_id.sigma_map (fun _ => Subtype.val_injective))

theorem giantSignedPerformedBirthAddress_value
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (d : GiantSignedBirthData P ell C batch) (a : GiantSignedPerformedBirth d) :
    giantSignedBirthValue d (giantSignedPerformedBirthAddress d a) =
      some (giantSignedPerformedBirthPrime d a) := by
  rcases a with a | a
  · rfl
  · rcases a with a | a
    · exact ite_eq_right a.2.2.property
    · rfl

theorem giantSignedPerformedBirthAddress_covers
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (d : GiantSignedBirthData P ell C batch) (a : GiantSignedBirthAddress B ell C batch)
    (ha : giantSignedBirthValue d a ≠ none) :
    ∃ b : GiantSignedPerformedBirth d, giantSignedPerformedBirthAddress d b = a := by
  rcases a with a | a
  · exact ⟨.inl a, rfl⟩
  · rcases a with a | a
    · have h : a.2.2 ∉ d.promoted a.1 a.2.1 := by
        intro h
        exact ha (ite_eq_left h)
      exact ⟨.inr (.inl ⟨a.1, a.2.1, a.2.2, h⟩), rfl⟩
    · exact ⟨.inr (.inr a), rfl⟩

theorem giantSignedBirthDistinct_iff_performedInjective
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (d : GiantSignedBirthData P ell C batch) :
    GiantSignedBirthDistinct d ↔ MarkedPerformedInjective (giantSignedBirthValue d) := by
  constructor
  · intro hd a ha b hb hab
    obtain ⟨a', rfl⟩ := giantSignedPerformedBirthAddress_covers d a ha
    obtain ⟨b', rfl⟩ := giantSignedPerformedBirthAddress_covers d b hb
    rw [giantSignedPerformedBirthAddress_value, giantSignedPerformedBirthAddress_value] at hab
    exact congrArg (giantSignedPerformedBirthAddress d) (hd (Option.some.inj hab))
  · intro hd a b hab
    apply giantSignedPerformedBirthAddress_injective d
    apply hd
    · change giantSignedBirthValue d (giantSignedPerformedBirthAddress d a) ≠ none
      rw [giantSignedPerformedBirthAddress_value]
      exact Option.some_ne_none _
    · change giantSignedBirthValue d (giantSignedPerformedBirthAddress d b) ≠ none
      rw [giantSignedPerformedBirthAddress_value]
      exact Option.some_ne_none _
    · rw [giantSignedPerformedBirthAddress_value, giantSignedPerformedBirthAddress_value, hab]

end
end ArtinMatthews
