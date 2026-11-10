module

public import ArtinMatthews.GiantTwoSidedRootLabelData
public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
public import ArtinMatthews.GiantTwoSidedPatternRunCompatibility
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

/-!
# Edge arithmetic from residue compatibility

The actual copied and auxiliary products determine divisibility of the
edge dilation. Congruence of adjacent offsets supplies the necessary
prime divisor directly in the independent residue model.
-/

namespace ArtinMatthews
open Finset
noncomputable section

/-- For an endpoint label, the auxiliary ban leaves exactly the copied
prime factors of the complete dilation. -/
theorem giantTwoSidedLabelDilation_dvd_iff_active {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k + ell)}
    {a : GiantTwoSidedPatternAuxiliary P C} (h : GiantTwoSidedLabelCompatible C s t a)
    (j : J) {p : ℕ} (hp : p ∈ markedPhysicalLabelSet s j ∨ p ∈ markedPhysicalLabelSet t j) :
    p ∣ giantTwoSidedPatternDilation C s a ↔
      p ∈ giantTwoSidedPatternCopiedValues (P j) (C j) (s j) := by
  have hpP : p ∈ P j := hp.elim (fun hs => markedPhysicalLabelSet_subset s j hs)
    (fun ht => markedPhysicalLabelSet_subset t j ht)
  have hprime := hP j p hpP
  have haux : ¬p ∣ giantTwoSidedPatternAuxiliaryProduct a := by
    intro hd
    obtain ⟨g, i, hi⟩ := (giantTwoSidedPatternAuxiliaryProduct_dvd_iff hP a hprime).mp hd
    rcases hp with hs | ht
    · obtain ⟨l, _, hl⟩ := mem_image.mp hs
      exact (h.banned g j i l).1 (hi.trans hl.symm)
    · obtain ⟨l, _, hl⟩ := mem_image.mp ht
      exact (h.banned g j i l).2 (hi.trans hl.symm)
  unfold giantTwoSidedPatternDilation
  rw [hprime.dvd_mul, or_iff_left haux]
  exact giantTwoSidedPatternCopiedProduct_dvd_iff hP hdis C s j hpP

/-- Equal residues at adjacent offsets force the prime into the dilation
when the signed shift has nonzero absolute value smaller than the prime. -/
theorem giantTwoSidedDilation_dvd_of_offset_congr {p D : ℕ} (hp : p.Prime)
    {step left right : ℤ} (hstep : 0 < step.natAbs) (hsize : step.natAbs < p)
    (hshift : right = left + step * (D : ℤ)) (hcongr : (right : ZMod p) = (left : ZMod p)) : p ∣ D := by
  have hcast : (right : ZMod p) = (left : ZMod p) + ((step * (D : ℤ) : ℤ) : ZMod p) := by
    rw [hshift, Int.cast_add]
  rw [hcongr] at hcast
  have hzero : ((step * (D : ℤ) : ℤ) : ZMod p) = 0 :=
    add_left_cancel (hcast.symm.trans (add_zero _).symm)
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (step * (D : ℤ)) p).mp hzero
  have hn : p ∣ step.natAbs * D := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact (hp.dvd_mul.mp hn).resolve_left (fun h => (not_le_of_gt hsize) (Nat.le_of_dvd hstep h))

/-- Common labels are the literal copied values of the edge. -/
theorem giantTwoSidedLabelCommon_eq_copied {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k + ell)}
    {a : GiantTwoSidedPatternAuxiliary P C} (h : GiantTwoSidedLabelCompatible C s t a)
    {step left right : ℤ} (hstep : 0 < step.natAbs) (hsize : ∀ j p, p ∈ P j → step.natAbs < p)
    (hshift : right = left + step * (giantTwoSidedPatternDilation C s a : ℤ))
    (j : J) (hcongr : ∀ p, p ∈ markedPhysicalLabelSet s j → p ∈ markedPhysicalLabelSet t j →
      (right : ZMod p) = (left : ZMod p)) :
    markedPhysicalLabelSet s j ∩ markedPhysicalLabelSet t j =
      giantTwoSidedPatternCopiedValues (P j) (C j) (s j) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs, ht⟩ := mem_inter.mp hp
    have hmem := markedPhysicalLabelSet_subset s j hs
    have hd := giantTwoSidedDilation_dvd_of_offset_congr (hP j p hmem) hstep
      (hsize j p hmem) hshift (hcongr p hs ht)
    exact (giantTwoSidedLabelDilation_dvd_iff_active hP hdis h j (Or.inl hs)).mp hd
  · intro hp
    obtain ⟨l, hl, he⟩ := mem_image.mp hp
    have ht := (congrArg Subtype.val (h.copied j l (mem_sdiff.mp hl).2)).trans he
    exact mem_inter.mpr ⟨mem_image.mpr ⟨Fin.castAdd ell l, mem_univ _, he⟩,
      mem_image.mpr ⟨Fin.castAdd ell l, mem_univ _, ht⟩⟩

/-- An injective marking puts a free slot outside the copied values. -/
theorem giantTwoSidedPatternFreeSlot_not_copiedValue (P : Finset ℕ) {k ell : ℕ}
    (C : Finset (Fin k)) (a : Fin (k + ell) → ↥P) (ha : Function.Injective a)
    (l : GiantTwoSidedPatternFreeSlots C ell) :
    (a (giantTwoSidedPatternFreeSlot C ell l)).val ∉ giantTwoSidedPatternCopiedValues P C a := by
  intro h
  obtain ⟨i, hi, he⟩ := mem_image.mp h
  have hval : a (Fin.castAdd ell i) = a (giantTwoSidedPatternFreeSlot C ell l) := Subtype.ext he
  have hind := ha hval
  cases l with
  | inl l =>
    change Fin.castAdd ell i = Fin.castAdd ell l.val at hind
    have hiEq := Fin.castAdd_injective k ell hind
    exact (mem_sdiff.mp hi).2 (by simpa only [hiEq] using l.property)
  | inr l =>
    have hnat := congrArg Fin.val hind
    change i.val = k + l.val at hnat
    omega

theorem giantTwoSidedLabelSourceFree_not_dvd {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k + ell)}
    {a : GiantTwoSidedPatternAuxiliary P C} (h : GiantTwoSidedLabelCompatible C s t a)
    (hs : MarkedPhysicalMarkingDistinct s) (j : J) (l : GiantTwoSidedPatternFreeSlots (C j) ell) :
    ¬(s j (giantTwoSidedPatternFreeSlot (C j) ell l)).val ∣ giantTwoSidedPatternDilation C s a := by
  let slot := giantTwoSidedPatternFreeSlot (C j) ell l
  have hp : (s j slot).val ∈ markedPhysicalLabelSet s j := mem_image.mpr ⟨slot, mem_univ _, rfl⟩
  intro hd
  exact giantTwoSidedPatternFreeSlot_not_copiedValue (P j) (C j) (s j) (hs j) l
    ((giantTwoSidedLabelDilation_dvd_iff_active hP hdis h j (Or.inl hp)).mp hd)

theorem giantTwoSidedLabelTargetFree_not_dvd {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k + ell)}
    {a : GiantTwoSidedPatternAuxiliary P C} (h : GiantTwoSidedLabelCompatible C s t a)
    (ht : MarkedPhysicalMarkingDistinct t) (j : J) (l : GiantTwoSidedPatternFreeSlots (C j) ell) :
    ¬(t j (giantTwoSidedPatternFreeSlot (C j) ell l)).val ∣ giantTwoSidedPatternDilation C s a := by
  let slot := giantTwoSidedPatternFreeSlot (C j) ell l
  have hp : (t j slot).val ∈ markedPhysicalLabelSet t j := mem_image.mpr ⟨slot, mem_univ _, rfl⟩
  intro hd
  apply giantTwoSidedPatternFreeSlot_not_copiedValue (P j) (C j) (t j) (ht j) l
  rw [giantTwoSidedPatternCopiedValues_eq h.copied j]
  exact (giantTwoSidedLabelDilation_dvd_iff_active hP hdis h j (Or.inr hp)).mp hd

end
end ArtinMatthews
