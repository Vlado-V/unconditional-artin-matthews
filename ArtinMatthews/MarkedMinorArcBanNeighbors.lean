module

public import ArtinMatthews.MarkedMinorArcDirtyAnchor
public import ArtinMatthews.MarkedMinorArcCellGeometry
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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


set_option backward.privateInPublic true
@[expose] public section

/-! Literal determinant-one neighbor enumeration, with the source constant33. -/
noncomputable section
namespace ArtinMatthews

def markedBanIntegerWindow (c R : ℝ) : Finset ℤ := Finset.Icc ⌈-R-c⌉ ⌊R-c⌋

theorem mem_markedBanIntegerWindow {c R : ℝ} {h : ℤ} :
    h ∈ markedBanIntegerWindow c R ↔ |(h:ℝ)+c| ≤ R := by
  rw [markedBanIntegerWindow,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor
  · rintro ⟨ha,hb⟩
    constructor <;> linarith
  · rintro ⟨ha,hb⟩
    constructor <;> linarith

theorem markedBanIntegerWindow_card_le (c : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((markedBanIntegerWindow c R).card:ℝ) ≤ 2*R+1 := by
  have hlo := Int.le_ceil (-R-c)
  have hhi := Int.floor_le (R-c)
  rw [markedBanIntegerWindow,Int.card_Icc]
  by_cases hz : 0 ≤ ⌊R-c⌋+1-⌈-R-c⌉
  · have hc : (((⌊R-c⌋+1-⌈-R-c⌉).toNat:ℕ):ℝ) = ((⌊R-c⌋+1-⌈-R-c⌉:ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz
    rw [hc]
    push_cast
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simp only [Nat.cast_zero]
    linarith

theorem markedBanIntegerWindow_card_le_33 (c : ℝ) : (markedBanIntegerWindow c 16).card ≤ 33 := by
  have hh := markedBanIntegerWindow_card_le c (by norm_num : (0:ℝ)≤16)
  norm_num at hh
  exact_mod_cast hh

def markedBanNeighborPositions (z w : ℤ × ℤ) (j : ℤ) (rstar : ℝ) : Finset (ℤ × ℤ) :=
  (markedBanIntegerWindow ((j:ℝ)*rstar) 16).image (fun h => markedMinorDirtyPosition z w h j)

theorem markedBanNeighborPositions_card_le (z w : ℤ × ℤ) (j : ℤ) (rstar : ℝ) :
    (markedBanNeighborPositions z w j rstar).card ≤ 33 :=
  Finset.card_image_le.trans (markedBanIntegerWindow_card_le_33 _)

theorem markedBan_neighbor_decomposition (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1) :
    v = markedMinorDirtyPosition z w (markedMinorIntegerDet v w) (markedMinorIntegerDet z v) := by
  have hh := markedMinorIntegerBasis_decompose z w v hd
  exact Prod.ext hh.1 hh.2

/-- The literal source tau ratio supplies the neighbor-window hypothesis. -/
theorem markedBan_neighbor_tau_identity (r : ℝ) (z w v : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0) :
    (markedMinorIntegerDet v w:ℝ)+(markedMinorIntegerDet z v:ℝ)*
      (markedMinorIntegerTau r w/markedMinorIntegerTau r z) =
        markedMinorIntegerTau r v/markedMinorIntegerTau r z := by
  obtain ⟨h₁,h₂⟩ := markedMinorIntegerBasis_decompose z w v hd
  simpa only [Nat.cast_one,one_mul] using markedMinorSharedLattice_shear r 1 z w v
    (markedMinorIntegerDet v w) (markedMinorIntegerDet z v)
    (by simpa only [Nat.cast_one,one_mul] using h₁)
    (by simpa only [Nat.cast_one,one_mul] using h₂) hz

theorem markedBan_mem_neighbors_of_tau (r : ℝ) (z w v : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) :
    v ∈ markedBanNeighborPositions z w (markedMinorIntegerDet z v)
      (markedMinorIntegerTau r w/markedMinorIntegerTau r z) := by
  apply Finset.mem_image.mpr
  refine ⟨markedMinorIntegerDet v w,mem_markedBanIntegerWindow.mpr ?_,
    (markedBan_neighbor_decomposition z w v hd).symm⟩
  rwa [markedBan_neighbor_tau_identity r z w v hd hz]

/-- For fixed actual determinant, every target in the source box lies in
the constructed set of at most33 integer neighbors. -/
theorem markedBan_targets_card_le (r : ℝ) (z w : ℤ × ℤ) (j : ℤ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (V : Finset (ℤ × ℤ))
    (hV : ∀ v ∈ V, markedMinorIntegerDet z v=j ∧
      |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) : V.card ≤ 33 := by
  apply (Finset.card_le_card ?_).trans (markedBanNeighborPositions_card_le z w j
    (markedMinorIntegerTau r w/markedMinorIntegerTau r z))
  intro v hv
  have hh := markedBan_mem_neighbors_of_tau r z w v hd hz (hV v hv).2
  rwa [(hV v hv).1] at hh

end ArtinMatthews
