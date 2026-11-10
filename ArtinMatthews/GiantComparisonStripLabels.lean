module

public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantTwoSidedPatternRunCompatibility
public import ArtinMatthews.MarkedPhysicalEndpointRecovery
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

/-! The shared and free coordinates of a physical comparison pattern are
ordered by the original slots. The free coordinates include the pad slots. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

abbrev GiantComparisonSharedLabels {J : Type*} (P : J → Finset ℕ) {k : ℕ}
    (C : J → Finset (Fin k)) := (j : J) → ↥(univ \ C j) → ↥(P j)

abbrev GiantComparisonFreeLabels {J : Type*} (P : J → Finset ℕ) {k : ℕ}
    (C : J → Finset (Fin k)) (ell : ℕ) :=
  (j : J) → GiantTwoSidedPatternFreeSlots (C j) ell → ↥(P j)

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}

def giantComparisonSharedLabelsOf (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) : GiantComparisonSharedLabels P C :=
  fun j i => a j (Fin.castAdd ell i.val)

def giantComparisonFreeLabelsOf (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) : GiantComparisonFreeLabels P C ell :=
  fun j i => a j (giantTwoSidedPatternFreeSlot (C j) ell i)

def giantComparisonJoinLabels (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) : MarkedPhysicalMarking P (k+ell) :=
  fun j => Fin.addCases (fun i =>
    if hi : i ∈ C j then b j (Sum.inl ⟨i, hi⟩)
    else c j ⟨i, mem_sdiff.mpr ⟨mem_univ i, hi⟩⟩) (fun i => b j (Sum.inr i))

@[simp] theorem giantComparisonJoinLabels_shared (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) (j : J) (i : ↥(univ \ C j)) :
    giantComparisonJoinLabels c b j (Fin.castAdd ell i.val) = c j i := by
  simp [giantComparisonJoinLabels, (mem_sdiff.mp i.property).2]

@[simp] theorem giantComparisonJoinLabels_free (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) (j : J)
    (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    giantComparisonJoinLabels c b j (giantTwoSidedPatternFreeSlot (C j) ell i) = b j i := by
  cases i with
  | inl i => simp [giantComparisonJoinLabels, giantTwoSidedPatternFreeSlot, i.property]
  | inr i => simp [giantComparisonJoinLabels, giantTwoSidedPatternFreeSlot]

def giantComparisonLabelsEquiv (C : J → Finset (Fin k)) (ell : ℕ) :
    MarkedPhysicalMarking P (k+ell) ≃
      GiantComparisonSharedLabels P C × GiantComparisonFreeLabels P C ell where
  toFun a := (giantComparisonSharedLabelsOf C a, giantComparisonFreeLabelsOf C a)
  invFun p := giantComparisonJoinLabels p.1 p.2
  left_inv a := by
    funext j l
    refine Fin.addCases (m:=k) (n:=ell) ?_ ?_ l
    · intro i
      by_cases hi : i ∈ C j
      · exact giantComparisonJoinLabels_free _ _ j (Sum.inl ⟨i, hi⟩)
      · exact giantComparisonJoinLabels_shared _ _ j ⟨i, mem_sdiff.mpr ⟨mem_univ i, hi⟩⟩
    · intro i
      exact giantComparisonJoinLabels_free _ _ j (Sum.inr i)
  right_inv p := by
    apply Prod.ext
    · funext j i
      exact giantComparisonJoinLabels_shared p.1 p.2 j i
    · funext j i
      exact giantComparisonJoinLabels_free p.1 p.2 j i

theorem giantComparisonSharedLabelsOf_eq {a b : MarkedPhysicalMarking P (k+ell)}
    (h : ∀ j (i : Fin k), i ∉ C j → b j (Fin.castAdd ell i) = a j (Fin.castAdd ell i)) :
    giantComparisonSharedLabelsOf C b = giantComparisonSharedLabelsOf C a := by
  funext j i
  exact h j i.val (mem_sdiff.mp i.property).2

variable [Fintype J]

def giantComparisonSharedProduct (c : GiantComparisonSharedLabels P C) : ℕ :=
  ∏ j, ∏ i : ↥(univ \ C j), (c j i : ℕ)

theorem giantComparisonSharedProduct_pos (hP : ∀ j p, p ∈ P j → p.Prime)
    (c : GiantComparisonSharedLabels P C) : 0 < giantComparisonSharedProduct c :=
  prod_pos fun j _ => prod_pos fun i _ => (hP j _ (c j i).property).pos

theorem giantComparisonSharedProduct_eq_copied (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    giantComparisonSharedProduct (giantComparisonSharedLabelsOf C a) =
      giantTwoSidedPatternCopiedProduct C a := by
  apply prod_congr rfl
  intro j _
  exact prod_coe_sort (univ \ C j) (fun i : Fin k => (a j (Fin.castAdd ell i) : ℕ))

theorem giantComparisonSharedProduct_join (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) :
    giantTwoSidedPatternCopiedProduct C (giantComparisonJoinLabels c b) =
      giantComparisonSharedProduct c := by
  rw [← giantComparisonSharedProduct_eq_copied]
  congr 1
  funext j i
  exact giantComparisonJoinLabels_shared c b j i

theorem giantComparisonSharedLabel_dvd (c : GiantComparisonSharedLabels P C)
    (j : J) (i : ↥(univ \ C j)) : (c j i : ℕ) ∣ giantComparisonSharedProduct c :=
  (dvd_prod_of_mem (fun l : ↥(univ \ C j) => (c j l : ℕ)) (mem_univ i)).trans
    (dvd_prod_of_mem (fun g : J => ∏ l : ↥(univ \ C g), (c g l : ℕ)) (mem_univ j))

theorem giantComparisonSharedProduct_dvd (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (ha : MarkedPhysicalMarkingDistinct a)
    {n : ℕ} (hd : ∀ j l, (a j l : ℕ) ∣ n) :
    giantComparisonSharedProduct (giantComparisonSharedLabelsOf C a) ∣ n := by
  rw [giantComparisonSharedProduct_eq_copied]
  refine dvd_trans ?_ (markedPhysicalMarkingProduct_dvd hP hdis a ha hd)
  apply prod_dvd_prod_of_dvd
  intro j _
  have he := prod_map (univ \ C j) (Fin.castAddEmb ell) (fun l => (a j l : ℕ))
  simp only [Fin.castAddEmb_apply] at he
  rw [← he]
  exact prod_dvd_prod_of_subset _ _ _ (subset_univ _)

theorem giantComparisonFreeLabel_coprime (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (ha : MarkedPhysicalMarkingDistinct a)
    (j : J) (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    (giantComparisonFreeLabelsOf C a j i : ℕ).Coprime
      (giantComparisonSharedProduct (giantComparisonSharedLabelsOf C a)) := by
  let p := giantComparisonFreeLabelsOf C a j i
  apply (hP j p.val p.property).coprime_iff_not_dvd.mpr
  rw [giantComparisonSharedProduct_eq_copied, giantTwoSidedPatternCopiedProduct_dvd_iff hP hdis C a j p.property]
  rw [giantTwoSidedPatternCopiedValues, mem_image]
  rintro ⟨l, hl, he⟩
  have hslot : Fin.castAdd ell l = giantTwoSidedPatternFreeSlot (C j) ell i :=
    ha j (Subtype.ext he)
  have hlC := (mem_sdiff.mp hl).2
  cases i with
  | inl i =>
    change Fin.castAdd ell l = Fin.castAdd ell i.val at hslot
    exact hlC (Fin.castAdd_injective k ell hslot ▸ i.property)
  | inr i =>
    have hv := congrArg Fin.val hslot
    change l.val = k+i.val at hv
    omega

end
end ArtinMatthews
