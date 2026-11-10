module

public import ArtinMatthews.GiantComparisonCellSeparation
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealGroupedSlotCount
public import ArtinMatthews.IdealProductDyadicBounds
public import ArtinMatthews.IdealSelectedFibers
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! A retained logarithmic cell has an integer origin comparable to every
product in that cell. Nonempty free-slot sets give the large product scale. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def giantComparisonCellOrigin (h : ℝ) (j : ℤ) : ℕ :=
  ⌊Real.exp ((j : ℝ)*h)⌋₊

theorem giantComparisonCellOrigin_bounds {I : Type*} [Fintype I]
    (P : I → Finset ℕ) {h : ℝ} (hh : 0 < h) (hhexp : Real.exp h ≤ 2)
    (j : ℤ) (a : IdealSelectedLabels P) (hj : idealLogCell h a = j)
    {Y : ℝ} (hY : 4 ≤ Y) (hlo : Y ≤ (idealSelectedProduct a : ℝ)) :
    let U := giantComparisonCellOrigin h j
    Y/4 ≤ (U : ℝ) ∧ U ≤ idealSelectedProduct a ∧
      idealSelectedProduct a < U+4*U := by
  let t := Real.exp ((j : ℝ)*h)
  let U := giantComparisonCellOrigin h j
  have ht : 0 < t := Real.exp_pos _
  have hp : 0 < (idealSelectedProduct a : ℝ) := by linarith
  have hb := idealLogCell_bounds hh a
  rw [hj] at hb
  have hle : t ≤ (idealSelectedProduct a : ℝ) := by
    exact (Real.le_log_iff_exp_le hp).mp hb.1
  have hlt : (idealSelectedProduct a : ℝ) < 2*t := by
    calc
      _ < Real.exp (((j : ℝ)+1)*h) := (Real.log_lt_iff_lt_exp hp).mp hb.2
      _ = t*Real.exp h := by rw [show ((j : ℝ)+1)*h=(j : ℝ)*h+h by ring, Real.exp_add]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hhexp ht.le]
  have hfloor : (U : ℝ) ≤ t := Nat.floor_le ht.le
  have hceil : t < (U : ℝ)+1 := Nat.lt_floor_add_one t
  have hU : Y/4 ≤ (U : ℝ) := by linarith
  have hU1 : 1 ≤ (U : ℝ) := by linarith
  refine ⟨hU, ?_, ?_⟩
  · exact_mod_cast hfloor.trans hle
  · exact_mod_cast (show (idealSelectedProduct a : ℝ) < (U : ℝ)+4*(U : ℝ) by linarith)

theorem giantComparisonCellOrigin_support {I : Type*} [Fintype I]
    (P : I → Finset ℕ) {h : ℝ} (hh : 0 < h) (hhexp : Real.exp h ≤ 2)
    (j : ℤ) {Y : ℝ} (hY : 4 ≤ Y)
    (hlo : ∀ a : IdealSelectedLabels P, Y ≤ (idealSelectedProduct a : ℝ))
    {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P)
    (ha : idealSelectedProduct a ∉ Ico (giantComparisonCellOrigin h j)
      (giantComparisonCellOrigin h j+4*giantComparisonCellOrigin h j)) :
    giantComparisonCellFreeTest P h j χ a = 0 := by
  apply giantComparisonCellFreeTest_zero_of_ne
  intro hj
  obtain ⟨_,hl,hu⟩ := giantComparisonCellOrigin_bounds P hh hhexp j a hj hY (hlo a)
  exact ha (mem_Ico.mpr ⟨hl,hu⟩)

theorem giantComparisonSelected_card_le {G : Type*} [Fintype G] [DecidableEq G]
    {k : ℕ} (A : Finset (G × Fin k)) (m : ℕ)
    (hm : ∀ g, (idealResidualFreeSlots A g).card ≤ m) :
    Fintype.card (↥A) ≤ m*Fintype.card G := by
  rw [← Fintype.card_congr (idealSelectedNumberedIndexEquiv A)]
  exact idealGroupedSlot_card_le (fun g => (idealResidualFreeSlots A g).card) m hm

theorem giantComparisonSelected_product_lower {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A : Finset (G × Fin k)) (hA : A.Nonempty)
    (hP : ∀ g p, p ∈ P g → p.Prime) (Y : ℝ)
    (hY : ∀ g p, p ∈ P g → Y ≤ (p : ℝ))
    (a : IdealSelectedLabels (idealResidualBands P A)) :
    Y ≤ (idealSelectedProduct a : ℝ) := by
  obtain ⟨i,hi⟩ := hA
  let v : ↥A := ⟨i,hi⟩
  have h := idealSelectedProduct_ge_prime (idealResidualBands P A)
    (fun j p hp => hP j.val.1 p hp) a v
  exact (hY i.1 _ (a v).property).trans (by exact_mod_cast h)

end
end ArtinMatthews
