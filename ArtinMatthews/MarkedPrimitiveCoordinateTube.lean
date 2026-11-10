module

public import ArtinMatthews.MarkedMinorArcSharedLattice
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import ArtinMatthews.MarkedPrimitiveCoordinateCompletion
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

/-! A literal finite integer tube for primitive relative positions,
with its actual cardinality and bounded determinant-one complements. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPrimitiveCoordinateTube (B : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(B:ℤ)) B) ×ˢ (Finset.Icc (-(B:ℤ)) B)).filter
    (fun z => IsCoprime z.1 z.2)

theorem markedPrimitiveCoordinateTube_mem (B : ℕ) (z : ℤ × ℤ) :
    z∈markedPrimitiveCoordinateTube B ↔ |z.1|≤(B:ℤ) ∧ |z.2|≤(B:ℤ) ∧ IsCoprime z.1 z.2 := by
  simp only [markedPrimitiveCoordinateTube,Finset.mem_filter,Finset.mem_product,
    Finset.mem_Icc,abs_le]
  tauto

theorem markedPrimitiveCoordinateTube_card_le (B : ℕ) :
    (markedPrimitiveCoordinateTube B).card≤(2*B+1)^2 := by
  have hc : (Finset.Icc (-(B:ℤ)) B).card=2*B+1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((Finset.Icc (-(B:ℤ)) B) ×ˢ (Finset.Icc (-(B:ℤ)) B)).card := Finset.card_filter_le _ _
    _ = _ := by rw [Finset.card_product,hc]; ring

theorem markedPrimitiveCoordinateTube_of_real_bound (B : ℕ) (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) (h₁ : |(z.1:ℝ)|≤B) (h₂ : |(z.2:ℝ)|≤B) :
    z∈markedPrimitiveCoordinateTube B := by
  apply (markedPrimitiveCoordinateTube_mem B z).mpr
  exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,hz⟩

theorem markedPrimitiveCoordinateTube_complement (B : ℕ) (z : markedPrimitiveCoordinateTube B) :
    ∃ w : ℤ × ℤ,markedMinorIntegerDet z.1 w=1 ∧
      |(w.1:ℝ)|≤(B:ℝ)+1 ∧ |(w.2:ℝ)|≤(B:ℝ)+1 := by
  have hz := (markedPrimitiveCoordinateTube_mem B z.1).mp z.2
  refine ⟨markedPrimitiveCoordinateCompletion z.1 hz.2.2,
    markedPrimitiveCoordinateCompletion_det z.1 hz.2.2,?_⟩
  exact markedPrimitiveCoordinateCompletion_real_bound z.1 hz.2.2 B
    (by exact_mod_cast hz.1) (by exact_mod_cast hz.2.1)

theorem markedPrimitiveCoordinateTube_path_card_le (B n : ℕ) :
    Fintype.card (Fin (n+1) → ↥(markedPrimitiveCoordinateTube B))≤(2*B+1)^(2*(n+1)) := by
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
  calc
    _ ≤ ((2*B+1)^2)^(n+1) := Nat.pow_le_pow_left (markedPrimitiveCoordinateTube_card_le B) (n+1)
    _ = _ := (pow_mul _ _ _).symm

end
end ArtinMatthews
