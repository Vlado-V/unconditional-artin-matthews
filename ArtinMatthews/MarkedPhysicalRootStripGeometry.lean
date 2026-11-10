module

public import ArtinMatthews.MarkedPhysicalTargetStrip
public import ArtinMatthews.FixedURootPrescribedMatrix
public import ArtinMatthews.FixedURootReciprocal
public import ArtinMatthews.FixedURootWeightedGeometry
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

/-! Exact intersection of a target strip and a source bad-root interval,
inside the actual canonical integer-root set. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fixedURootMatrixBox_mem_ratio {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (hA : 1 < A) (hα : 0 ≤ α) (hβ : β ≤ 1)
    (p : Σ _u : ℤ, ℤ × ℤ) :
    p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true true true true true ↔
      p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true ∧
        (p.2.1 : ℝ)/(p.1 : ℝ) ∈ Set.Icc α β := by
  rcases p with ⟨u,c,v⟩
  by_cases hu : (0 : ℤ) < u
  · have huR : (0 : ℝ) < u := by exact_mod_cast hu
    simp only [fixedURootMatrixBoxPoints, fixedURootReciprocal_mem_box hu,
      fixedURootReciprocal_scaled_interval huR, ite_true, Set.mem_Icc]
    constructor
    · rintro ⟨huI,hr,hvI,hur,hcr,hvr,hd⟩
      exact ⟨⟨huI,⟨hα.trans hr.1,hr.2.trans hβ⟩,hvI,hur,hcr,hvr,hd⟩,hr⟩
    · rintro ⟨⟨huI,_,hvI,hur,hcr,hvr,hd⟩,hr⟩
      exact ⟨huI,hr,hvI,hur,hcr,hvr,hd⟩
  · have hnone (a b : ℝ) : (⟨u,(c,v)⟩ : Σ _u : ℤ, ℤ × ℤ) ∉
        fixedURootMatrixBoxPoints g₀ A B a b C D true true true true true true := by
      intro hp
      have hh := (fixedURootMatrixBox_coordinate_bounds g₀ A B a b C D true true _ hp).1.1
      have hpR : (0 : ℝ) < u := lt_of_lt_of_le (lt_trans zero_lt_one hA) hh
      exact hu (by exact_mod_cast hpR)
    simp only [hnone α β, hnone 0 1, false_and]

def markedPhysicalRootStripPoints {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (z : ℤ × ℤ) : Finset (Σ _u : ℤ, ℤ × ℤ) := by
  classical
  exact (fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true).filter
    (fun p => (p.2.1 : ℝ)/(p.1 : ℝ) ∈ Set.Icc α β ∧
      |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16)

/-- The strip restriction is literally one clipped root interval, or the
empty set. No boundary points or zero-frequency targets are discarded. -/
theorem markedPhysicalRootStripPoints_eq {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (z : ℤ × ℤ) (hA : 1 < A) (hα : 0 ≤ α) (hβ : β ≤ 1) :
    markedPhysicalRootStripPoints g₀ A B α β C D z =
      if markedPhysicalStripArcActive z α β then
        fixedURootMatrixBoxPoints g₀ A B (markedPhysicalStripArcLower z α)
          (markedPhysicalStripArcUpper z β) C D true true true true true true
      else ∅ := by
  classical
  by_cases ha : markedPhysicalStripArcActive z α β
  · rw [ite_eq_left ha]
    have hb := markedPhysicalStripArc_bounds z hα hβ ha
    ext p
    rw [markedPhysicalRootStripPoints, Finset.mem_filter,
      fixedURootMatrixBox_mem_ratio g₀ A B (markedPhysicalStripArcLower z α)
        (markedPhysicalStripArcUpper z β) C D hA hb.1 hb.2.2 p,
      markedPhysicalTargetStrip_intersection]
    simp only [ha, true_and]
  · rw [ite_eq_right ha]
    ext p
    simp only [markedPhysicalRootStripPoints, Finset.mem_filter, Finset.notMem_empty,
      markedPhysicalTargetStrip_intersection, ha, false_and, and_false]

end ArtinMatthews
