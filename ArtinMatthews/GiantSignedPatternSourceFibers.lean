module

public import ArtinMatthews.GiantSignedCopiedTarget
public import ArtinMatthews.GiantSignedEdgeRealPairing
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

/-! The full active law splits exactly into its copied coordinates and
its ordered free tuple, without any normalization of the prime law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

abbrev GiantSignedPatternCopiedLabels (P : J → Finset ℕ) (C : J → Finset (Fin k)) :=
  (j : J) → {i : Fin k // i ∉ C j} → P j

def giantSignedPatternSourceFill (C : J → Finset (Fin k))
    (c : GiantSignedPatternCopiedLabels P C)
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    MarkedPhysicalMarking P (k+ell) :=
  fun j => Fin.addCases
    (fun i => if hi : i ∈ C j then
      t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm (Sum.inl ⟨i, hi⟩))
      else c j ⟨i, hi⟩)
    (fun i => t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm (Sum.inr i)))

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternSourceFill_copied (C : J → Finset (Fin k))
    (c : GiantSignedPatternCopiedLabels P C)
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card))
    (j : J) (i : {i : Fin k // i ∉ C j}) :
    giantSignedPatternSourceFill C c t j (Fin.castAdd ell i.val) = c j i := by
  simp only [giantSignedPatternSourceFill, Fin.addCases_left, dite_eq_right i.property]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternSourceFill_free (C : J → Finset (Fin k))
    (c : GiantSignedPatternCopiedLabels P C)
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card))
    (j : J) (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    giantSignedPatternSourceFill C c t j (giantTwoSidedPatternFreeSlot (C j) ell i) =
      t j ((giantSignedPatternFreeSlotEquiv (C j) ell).symm i) := by
  cases i with
  | inl i =>
      simp only [giantTwoSidedPatternFreeSlot, Sum.elim_inl, giantSignedPatternSourceFill,
        Fin.addCases_left, dite_eq_left i.property]
  | inr i =>
      simp only [giantTwoSidedPatternFreeSlot, Sum.elim_inr, giantSignedPatternSourceFill,
        Fin.addCases_right]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternSourceFill_freeLabels (C : J → Finset (Fin k))
    (c : GiantSignedPatternCopiedLabels P C)
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    giantSignedPatternFreeLabels C (giantSignedPatternSourceFill C c t) = t := by
  funext j i
  unfold giantSignedPatternFreeLabels
  rw [giantSignedPatternSourceFill_free, Equiv.symm_apply_apply]

def giantSignedPatternSourceEquiv (C : J → Finset (Fin k)) :
    MarkedPhysicalMarking P (k+ell) ≃
      GiantSignedPatternCopiedLabels P C ×
        GiantSignedPrimeTuple P (fun j => ell + (C j).card) where
  toFun a := (fun j i => a j (Fin.castAdd ell i.val), giantSignedPatternFreeLabels C a)
  invFun p := giantSignedPatternSourceFill C p.1 p.2
  left_inv a := by
    funext j i
    refine Fin.addCases ?_ ?_ i
    · intro i
      by_cases hi : i ∈ C j
      · simp only [giantSignedPatternSourceFill, Fin.addCases_left, dite_eq_left hi,
          giantSignedPatternFreeLabels, Equiv.apply_symm_apply,
          giantTwoSidedPatternFreeSlot, Sum.elim_inl]
      · simp only [giantSignedPatternSourceFill, Fin.addCases_left, dite_eq_right hi]
    · intro i
      simp only [giantSignedPatternSourceFill, Fin.addCases_right,
        giantSignedPatternFreeLabels, Equiv.apply_symm_apply,
        giantTwoSidedPatternFreeSlot, Sum.elim_inr]
  right_inv p := by
    apply Prod.ext
    · funext j i
      exact giantSignedPatternSourceFill_copied C p.1 p.2 j i
    · exact giantSignedPatternSourceFill_freeLabels C p.1 p.2

def giantSignedPatternCopiedMass (ν : (j : J) → P j → ℝ)
    {C : J → Finset (Fin k)} (c : GiantSignedPatternCopiedLabels P C) : ℝ :=
  ∏ j, ∏ i, ν j (c j i)

omit [DecidableEq J] in
theorem giantSignedPatternSourceFill_mass (ν : (j : J) → P j → ℝ)
    (C : J → Finset (Fin k)) (c : GiantSignedPatternCopiedLabels P C)
    (t : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    giantSignedActiveMass ν (giantSignedPatternSourceFill C c t) =
      giantSignedPatternCopiedMass ν c * giantSignedFreePrimeRealMass ν t := by
  unfold giantSignedActiveMass giantSignedPatternCopiedMass giantSignedFreePrimeRealMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_add,
    ← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin k => i ∉ C j)]
  have hc : (∏ i : {i : Fin k // i ∉ C j},
      ν j (giantSignedPatternSourceFill C c t j (Fin.castAdd ell i.val))) =
      ∏ i, ν j (c j i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [giantSignedPatternSourceFill_copied]
  rw [hc]
  rw [mul_assoc]
  congr 1
  have hf := Equiv.prod_comp (giantSignedPatternFreeSlotEquiv (C j) ell).symm
    (fun i => ν j (t j i))
  rw [Fintype.prod_sum_type] at hf
  rw [← hf]
  congr 1
  · apply Fintype.prod_equiv (Equiv.subtypeEquivRight (fun i : Fin k => not_not))
    intro i
    simp only [giantSignedPatternSourceFill, Fin.addCases_left]
    rw [dite_eq_left (not_not.mp i.property)]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (ν j) (giantSignedPatternSourceFill_free C c t j (Sum.inr i))

theorem giantSignedPatternSource_sum (ν : (j : J) → P j → ℝ)
    (C : J → Finset (Fin k)) (F : MarkedPhysicalMarking P (k+ell) → ℝ) :
    (∑ a : MarkedPhysicalMarking P (k+ell), giantSignedActiveMass ν a * F a) =
      ∑ c : GiantSignedPatternCopiedLabels P C, giantSignedPatternCopiedMass ν c *
        ∑ t : GiantSignedPrimeTuple P (fun j => ell + (C j).card),
          giantSignedFreePrimeRealMass ν t * F (giantSignedPatternSourceFill C c t) := by
  rw [← (giantSignedPatternSourceEquiv (P := P) (ell := ell) C).symm.sum_comp]
  simp only [Fintype.sum_prod_type, giantSignedPatternSourceEquiv,
    Equiv.coe_fn_symm_mk, giantSignedPatternSourceFill_mass, Finset.mul_sum, mul_assoc]

omit [Fintype J] [DecidableEq J] in
theorem giantSignedPatternSourceFill_patternFill (C : J → Finset (Fin k))
    (c : GiantSignedPatternCopiedLabels P C)
    (a b : GiantSignedPrimeTuple P (fun j => ell + (C j).card)) :
    giantSignedPatternFill C (giantSignedPatternSourceFill C c a) b =
      giantSignedPatternSourceFill C c b := by
  funext j i
  refine Fin.addCases ?_ ?_ i
  · intro i
    by_cases hi : i ∈ C j
    · simp only [giantSignedPatternFill, giantSignedPatternSourceFill,
        Fin.addCases_left, dite_eq_left hi]
    · simp only [giantSignedPatternFill, giantSignedPatternSourceFill,
        Fin.addCases_left, dite_eq_right hi]
  · intro i
    simp only [giantSignedPatternFill, giantSignedPatternSourceFill, Fin.addCases_right]

end
end ArtinMatthews
