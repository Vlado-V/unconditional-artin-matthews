module

public import ArtinMatthews.GiantSignedLifespanOriginalPath
public import ArtinMatthews.GiantSmallBigResidueSplit
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

/-! The original guarded path is a finite subtype of the literal
slot permutations, auxiliary coordinates, labels and small residues. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) {k n : ℕ} (ell : ℕ)
    (C : Fin n → B → Finset (Fin k))

abbrev GiantSignedLifespanPathSlots :=
  (Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))) ×
  (Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))) ×
  ((i : Fin n) → GiantTwoSidedPatternAuxiliary (Sum.elim PS PB)
    (giantSignedChronologicalJoinedPattern C i))

abbrev GiantSignedLifespanRawPath :=
  GiantSignedLifespanPathSlots PS PB ell C ×
    (Fin (n+1) → MarkedPhysicalMarking (Sum.elim PS PB) (k+ell)) × GiantTwoSidedFullResidue PS

variable {PS PB ell C}

def GiantSignedLifespanRawPath.offset (raw : GiantSignedLifespanRawPath PS PB ell C)
    (κ : Fin n → ℤ) : Fin (n+1) → ℤ :=
  giantTwoSidedPathOffset (giantTwoSidedLabelIncrement (ell := ell)
    (giantSignedChronologicalJoinedPattern C) raw.2.1 raw.1.1 raw.1.2.2 κ)

def GiantSignedLifespanRawPath.valid (raw : GiantSignedLifespanRawPath PS PB ell C)
    (κ : Fin n → ℤ) : Prop :=
  GiantTwoSidedStaticLabels (giantSignedChronologicalJoinedPattern C) raw.1.1 raw.1.2.1 raw.1.2.2 raw.2.1 ∧
    GiantTwoSidedActiveCompatible univ raw.2.1 (raw.offset κ) ∧
    GiantSignedFullPrimeActive (giantSignedSmallMarking raw.2.1) (raw.offset κ) raw.2.2

def giantSignedLifespanOriginalPathRawEquiv (κ : Fin n → ℤ) :
    GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ ≃
      {raw : GiantSignedLifespanRawPath PS PB ell C // raw.valid κ} where
  toFun path := ⟨⟨⟨path.sourcePermutation,path.targetPermutation,path.auxiliary⟩,
    path.labels,path.smallRoot⟩,path.static,path.compatible,path.smallHits⟩
  invFun raw := ⟨raw.val.2.1,raw.val.1.1,raw.val.1.2.1,raw.val.1.2.2,
    raw.property.1,raw.property.2.1,raw.val.2.2,raw.property.2.2⟩
  left_inv path := by cases path; rfl
  right_inv raw := by rcases raw with ⟨⟨⟨π,τ,aux⟩,labels,root⟩,valid⟩; rfl

instance instFiniteGiantSignedLifespanOriginalPath
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] (κ : Fin n → ℤ) :
    Finite (GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ) := by
  classical
  exact Finite.of_injective (giantSignedLifespanOriginalPathRawEquiv κ)
    (giantSignedLifespanOriginalPathRawEquiv κ).injective

instance instFintypeGiantSignedLifespanOriginalPath
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] (κ : Fin n → ℤ) :
    Fintype (GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ) := Fintype.ofFinite _

@[instance_reducible] def giantSignedLifespanRawPathFintype [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] :
    Fintype (GiantSignedLifespanRawPath PS PB ell C) :=
  let perms : Fintype (Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))) := inferInstance
  let aux : Fintype ((i : Fin n) → GiantTwoSidedPatternAuxiliary (Sum.elim PS PB)
    (giantSignedChronologicalJoinedPattern C i)) := inferInstance
  let labels : Fintype (Fin (n+1) → MarkedPhysicalMarking (Sum.elim PS PB) (k+ell)) := inferInstance
  let roots : Fintype (GiantTwoSidedFullResidue PS) := inferInstance
  @instFintypeProd _ _ (@instFintypeProd _ _ perms (@instFintypeProd _ _ perms aux))
    (@instFintypeProd _ _ labels roots)

theorem giantSignedLifespanOriginalPath_sum_guarded {R : Type*} [AddCommMonoid R]
    [DecidableEq S] [DecidableEq B] [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (κ : Fin n → ℤ) (f : GiantSignedLifespanRawPath PS PB ell C → R) :
    letI := giantSignedLifespanRawPathFintype (PS := PS) (PB := PB) (ell := ell) (C := C)
    (∑ raw, if raw.valid κ then f raw else 0) =
      ∑ path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ,
        f ((giantSignedLifespanOriginalPathRawEquiv κ path).val) := by
  letI := giantSignedLifespanRawPathFintype (PS := PS) (PB := PB) (ell := ell) (C := C)
  let valid (raw : GiantSignedLifespanRawPath PS PB ell C) := raw.valid κ
  let e := giantSignedLifespanOriginalPathRawEquiv (PS := PS) (PB := PB) (ell := ell) (C := C) κ
  have hmem (raw : GiantSignedLifespanRawPath PS PB ell C) : raw ∈ univ.filter valid ↔ valid raw :=
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ raw,h⟩⟩
  have hs := Finset.sum_subtype (p := valid) (F := inferInstance) (univ.filter valid) hmem f
  change (∑ raw, if valid raw then f raw else 0) = ∑ path, f (e path).val
  rw [← Finset.sum_filter,hs]
  exact (e.sum_comp (fun raw => f raw.val)).symm

end
end ArtinMatthews
