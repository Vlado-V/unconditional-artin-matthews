module

public import ArtinMatthews.MarkedTypeIIGoodSecond
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Positive elementary-arc majorants for the actual bad tests. These
avoid expanding a threshold event into exponentially many Boolean cells. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedFiniteUnion_indicator_le {ι : Type*} [Fintype ι]
    (E : ι → Set (AddCircle (1:ℝ))) (θ : AddCircle (1:ℝ)) :
    (if θ ∈ ⋃ i,E i then (1:ℝ) else 0) ≤ ∑ i,if θ ∈ E i then (1:ℝ) else 0 := by
  by_cases h : θ ∈ ⋃ i,E i
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
    rw [ite_eq_left h]
    have hs := Finset.single_le_sum (f := fun j => if θ ∈ E j then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

def markedPairRootArcSet (Q : Finset ℤ) (T : ℤ) (ε : ℝ) (pair : Q × Q) : Set (AddCircle (1:ℝ)) :=
  if pair.1.1 = pair.2.1 then ∅ else markedBadRootMultiple ((pair.1.1-pair.2.1)*T) ε

theorem markedPairBadRoots_eq_arc_union (Q : Finset ℤ) (T : ℤ) (ε : ℝ) :
    markedPairBadRoots Q T ε = ⋃ p : Q × Q,markedPairRootArcSet Q T ε p := by
  ext θ
  constructor
  · intro h
    obtain ⟨u,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hu,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨v,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hv,h⟩ := Set.mem_iUnion.mp h
    apply Set.mem_iUnion.mpr
    exact ⟨(⟨u,hu⟩,⟨v,hv⟩),h⟩
  · intro h
    obtain ⟨⟨u,v⟩,h⟩ := Set.mem_iUnion.mp h
    apply Set.mem_iUnion.mpr
    refine ⟨u.1,Set.mem_iUnion.mpr ⟨u.2,Set.mem_iUnion.mpr ⟨v.1,Set.mem_iUnion.mpr ⟨v.2,?_⟩⟩⟩⟩
    exact h

def markedPairRootArcMajorant (Q : Finset ℤ) (T : ℤ) (ε : ℝ) (θ : AddCircle (1:ℝ)) : ℝ :=
  ∑ p : Q × Q,if θ ∈ markedPairRootArcSet Q T ε p then 1 else 0

theorem markedPairBadRoots_indicator_le_arcs (Q : Finset ℤ) (T : ℤ) (ε : ℝ)
    (θ : AddCircle (1:ℝ)) :
    (if θ ∈ markedPairBadRoots Q T ε then (1:ℝ) else 0) ≤ markedPairRootArcMajorant Q T ε θ := by
  rw [markedPairBadRoots_eq_arc_union]
  exact markedFiniteUnion_indicator_le _ θ

theorem markedPairFailureProbability_le_arcs {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (ε : ℝ) (θ : AddCircle (1:ℝ)) :
    markedPairFailureProbability Q T w ε θ ≤ ∑ i,w i*markedPairRootArcMajorant Q (T i) ε θ := by
  unfold markedPairFailureProbability
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (markedPairBadRoots_indicator_le_arcs Q (T i) ε θ) (hw i)
  by_cases hi : θ ∈ markedPairBadRoots Q (T i) ε <;> simpa [hi] using h

theorem markedPairThreshold_indicator_le_arcs {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (ε : ℝ) {η : ℝ} (hη : 0 < η) (θ : AddCircle (1:ℝ)) :
    (if η ≤ markedPairFailureProbability Q T w ε θ then (1:ℝ) else 0) ≤
      (∑ i,w i*markedPairRootArcMajorant Q (T i) ε θ)/η := by
  have hp := markedPairFailureProbability_nonneg Q T w hw ε θ
  have ha := markedPairFailureProbability_le_arcs Q T w hw ε θ
  by_cases h : η ≤ markedPairFailureProbability Q T w ε θ
  · rw [ite_eq_left h]
    exact (le_div_iff₀ hη).mpr (by simpa only [one_mul] using h.trans ha)
  · rw [ite_eq_right h]
    exact div_nonneg (hp.trans ha) hη.le

def markedFirstRootArcSet {ι : Type*} (D : ι → ℕ) (L : ℕ) (ε : ℝ)
    (pair : ι × ↥(Finset.Icc 1 L)) : Set (AddCircle (1:ℝ)) :=
  markedBadRootMultiple ((D pair.1*pair.2.1:ℕ):ℤ) ε

theorem markedFirstBadRoots_eq_arc_union {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (L : ℕ) (ε : ℝ) :
    markedFirstBadRoots D L ε = ⋃ p : ι × ↥(Finset.Icc 1 L),markedFirstRootArcSet D L ε p := by
  ext θ
  constructor
  · intro h
    obtain ⟨i,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨l,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hl,h⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨(i,⟨l,hl⟩),h⟩
  · intro h
    obtain ⟨⟨i,l⟩,h⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨l.1,Set.mem_iUnion.mpr ⟨l.2,h⟩⟩⟩

theorem markedFirstBadRoots_indicator_le_arcs {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (L : ℕ) (ε : ℝ) (θ : AddCircle (1:ℝ)) :
    (if θ ∈ markedFirstBadRoots D L ε then (1:ℝ) else 0) ≤
      ∑ p : ι × ↥(Finset.Icc 1 L),if θ ∈ markedFirstRootArcSet D L ε p then (1:ℝ) else 0 := by
  rw [markedFirstBadRoots_eq_arc_union]
  exact markedFiniteUnion_indicator_le _ θ

end
end ArtinMatthews
