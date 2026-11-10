module

public import ArtinMatthews.FixedURootFirstColumns
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact restriction of the canonical root set to coordinate tails.
The canonical completion, all congruences and the root-ratio interval are
unchanged by these finite restrictions. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError

theorem fixedURoot_mem_closed_interval (a b : ℝ) (n : ℤ) :
    n ∈ realIntervalIntegers a b true true ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp [realIntervalIntegers, Int.ceil_le, Int.le_floor]

theorem fixedURootMatrixBox_coordinate_bounds {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool)
    (p : Σ _u : ℤ, ℤ × ℤ)
    (hp : p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true) :
    (p.1 : ℝ) ∈ Set.Icc A B ∧ (p.2.2 : ℝ) ∈ Set.Icc C D := by
  rcases p with ⟨u,c,v⟩
  simp only [fixedURootMatrixBoxPoints, fixedURootBoxPoints, Finset.mem_sigma,
    fixedURootBoxIndices, fixedURootPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    fixedURoot_mem_closed_interval] at hp
  exact ⟨hp.1.1, hp.2.1.2⟩

theorem fixedURootMatrixBox_filter_tails {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D t s : ℝ) (lcR rcR : Bool)
    (ht : t ∈ Set.Icc A B) (hs : s ∈ Set.Icc C D) :
    (fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true).filter
      (fun p => t ≤ (p.1 : ℝ) ∧ s ≤ (p.2.2 : ℝ)) =
        fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true := by
  ext p
  rcases p with ⟨u,c,v⟩
  simp only [fixedURootMatrixBoxPoints, fixedURootBoxPoints, Finset.mem_sigma,
    fixedURootBoxIndices, fixedURootPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    fixedURoot_mem_closed_interval]
  constructor
  · rintro ⟨⟨⟨hu,hr⟩,⟨⟨hc,hv⟩,hm⟩⟩,htu,hsv⟩
    exact ⟨⟨⟨htu,hu.2⟩,hr⟩,⟨⟨hc,⟨hsv,hv.2⟩⟩,hm⟩⟩
  · rintro ⟨⟨hu,hr⟩,⟨⟨hc,hv⟩,hm⟩⟩
    exact ⟨⟨⟨⟨ht.1.trans hu.1,hu.2⟩,hr⟩,
      ⟨⟨hc,⟨hs.1.trans hv.1,hv.2⟩⟩,hm⟩⟩,hu.1,hv.1⟩

/-- Weighted sums also forget the unique canonical completion without
multiplicity: the counted objects are actual primitive first columns. -/
theorem fixedURootMatrixFirstColumns_sum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (hA : 1 < A) (hC : 1 < C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (f : ℤ × ℤ → ℂ) :
    (∑ p ∈ fixedURootMatrixFirstColumns g₀ A B α β C D true true lcR rcR true true, f p) =
      ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true,
        f (fixedURootFirstColumn p) := by
  classical
  rw [fixedURootMatrixFirstColumns, Finset.sum_image]
  exact fixedURootFirstColumn_injOn hA hC hα hβ

end ArtinMatthews
