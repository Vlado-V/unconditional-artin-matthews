module

public import ArtinMatthews.GiantSignedEdgeStorePromote
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered free target labels determine exactly the full targets which
retain every original copied coordinate. Repetitions remain permitted. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}

def giantSignedPatternFill {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell))
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    MarkedPhysicalMarking P (k+ell) :=
  fun j => Fin.addCases
    (fun i => if h : i ∈ C j then
      t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm (Sum.inl ⟨i,h⟩))
      else a j (Fin.castAdd ell i))
    (fun i => t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm (Sum.inr i)))

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternFill_copied {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell))
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    IdealCopied C a (giantSignedPatternFill C a t) := by
  intro j i hi
  simp only [giantSignedPatternFill, Fin.addCases_left, dite_eq_right hi]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternFill_free {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell))
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card))
    (j : J) (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    giantSignedPatternFill C a t j (giantTwoSidedPatternFreeSlot (C j) ell i) =
      t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm i) := by
  cases i with
  | inl i =>
      simp only [giantTwoSidedPatternFreeSlot, Sum.elim_inl, giantSignedPatternFill,
        Fin.addCases_left, dite_eq_left i.property]
  | inr i =>
      simp only [giantTwoSidedPatternFreeSlot, Sum.elim_inr, giantSignedPatternFill,
        Fin.addCases_right]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternFreeLabels_fill {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell))
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    giantSignedPatternFreeLabels C (giantSignedPatternFill C a t) = t := by
  funext j i
  unfold giantSignedPatternFreeLabels
  rw [giantSignedPatternFill_free, Equiv.symm_apply_apply]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternFill_freeLabels {k ell : ℕ} (C : J → Finset (Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) (hb : IdealCopied C a b) :
    giantSignedPatternFill C a (giantSignedPatternFreeLabels C b) = b := by
  funext j i
  refine Fin.addCases ?_ ?_ i
  · intro i
    by_cases hi : i ∈ C j
    · simp only [giantSignedPatternFill, Fin.addCases_left, dite_eq_left hi,
        giantSignedPatternFreeLabels, Equiv.apply_symm_apply, giantTwoSidedPatternFreeSlot,
        Sum.elim_inl]
    · simpa only [giantSignedPatternFill, Fin.addCases_left, dite_eq_right hi] using (hb j i hi).symm
  · intro i
    simp only [giantSignedPatternFill, Fin.addCases_right, giantSignedPatternFreeLabels,
      Equiv.apply_symm_apply, giantTwoSidedPatternFreeSlot, Sum.elim_inr]

def giantSignedCopiedTargetEquiv {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    GiantSignedPrimeTuple P (fun j => ell + (C j).card) ≃
      {b : MarkedPhysicalMarking P (k+ell) // IdealCopied C a b} where
  toFun t := ⟨giantSignedPatternFill C a t, giantSignedPatternFill_copied C a t⟩
  invFun b := giantSignedPatternFreeLabels C b.val
  left_inv := giantSignedPatternFreeLabels_fill C a
  right_inv b := Subtype.ext (giantSignedPatternFill_freeLabels C a b.val b.property)

omit [DecidableEq J] in
theorem giantSignedPatternFill_mass {k ell : ℕ} (ν : (j : J) → P j → ℝ)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    giantSignedFreePrimeMass (fun j p => (ν j p : ℂ)) t =
      (idealFreshTargetMass ν C (giantSignedPatternFill C a t) : ℂ) := by
  unfold giantSignedFreePrimeMass idealFreshTargetMass
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.ofReal_prod]
  symm
  calc
    (∏ i : GiantTwoSidedPatternFreeSlots (C j) ell,
        (ν j (giantSignedPatternFill C a t j (giantTwoSidedPatternFreeSlot (C j) ell i)) : ℂ)) =
        ∏ i : GiantTwoSidedPatternFreeSlots (C j) ell,
          (ν j (t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm i)) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [giantSignedPatternFill_free]
    _ = _ := Equiv.prod_comp (giantSignedPatternFreeSlotEquiv (C j) ell).symm
      (fun i => (ν j (t j i) : ℂ))

theorem giantSignedCopiedTarget_sum {k ell : ℕ} (ν : (j : J) → P j → ℝ)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ t : GiantSignedPrimeTuple P (fun j => ell + (C j).card),
      giantSignedFreePrimeMass (fun j p => (ν j p : ℂ)) t * F (giantSignedPatternFill C a t)) =
      ∑ b : MarkedPhysicalMarking P (k+ell), if IdealCopied C a b then
        (idealFreshTargetMass ν C b : ℂ) * F b else 0 := by
  simp_rw [giantSignedPatternFill_mass ν C a]
  have he := (giantSignedCopiedTargetEquiv C a).sum_comp
    (fun b => (idealFreshTargetMass ν C b.val : ℂ) * F b.val)
  have hs := Finset.sum_subtype (p := IdealCopied C a) (F := inferInstance)
    (Finset.univ.filter (IdealCopied C a)) (by simp)
    (fun b => (idealFreshTargetMass ν C b : ℂ) * F b)
  exact he.trans (by simpa only [Finset.sum_filter] using hs.symm)

end
end ArtinMatthews
