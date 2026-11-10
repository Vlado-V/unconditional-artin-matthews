module

public import ArtinMatthews.MarkedRootPartitionCells
public import ArtinMatthews.FixedURootRatioAbel
public import ArtinMatthews.FixedURootWeightedGeometry
public import ArtinMatthews.MarkedRootPartitionIntegerIntervals
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The faithful normalized partition is the literal arithmetic root
partition with its matching half-open endpoint flags. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError
attribute [local instance] Classical.propDecidable

def markedRootNormalizedPoint (U V : ℝ) (p : Σ _u : ℤ,ℤ × ℤ) : ℝ × (ℝ × ℝ) :=
  (fixedURootRatio p,(p.1:ℝ)/U,(p.2.2:ℝ)/V)

def markedRootPartitionRootSet {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V : ℝ) (N : ℕ) (i : MarkedRootGridIndex N) : Finset (Σ _u : ℤ,ℤ × ℤ) :=
  fixedURootMatrixBoxPoints g₀
    (U*(1+(i.2.1:ℝ)/N)) (U*(1+((i.2.1:ℝ)+1)/N))
    ((i.1:ℝ)/N) (((i.1:ℝ)+1)/N)
    (V*(1+(i.2.2:ℝ)/N)) (V*(1+((i.2.2:ℝ)+1)/N))
    true (decide (i.2.1.val+1=15*N)) true (decide (i.1.val+1=N))
    true (decide (i.2.2.val+1=N))

theorem markedRootNormalizedPoint_mem_domain {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) {U V : ℝ}
    (hU : 1 < U) (hV : 1 < V) (p : Σ _u : ℤ,ℤ × ℤ)
    (hp : p ∈ fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true) :
    markedRootNormalizedPoint U V p ∈ markedRootBoxDomain := by
  have hb := fixedURootMatrixBox_coordinate_bounds g₀ U (16*U) 0 1 V (2*V) true true p hp
  refine ⟨fixedURootMatrixBox_ratio_bounds g₀ hU p hp,?_,?_⟩
  · change (p.1:ℝ)/U ∈ Set.Icc (1:ℝ) 16
    rw [Set.mem_Icc,le_div_iff₀ (by linarith : 0 < U),div_le_iff₀ (by linarith : 0 < U)]
    exact ⟨by simpa only [one_mul] using hb.1.1,hb.1.2⟩
  · change (p.2.2:ℝ)/V ∈ Set.Icc (1:ℝ) 2
    rw [Set.mem_Icc,le_div_iff₀ (by linarith : 0 < V),div_le_iff₀ (by linarith : 0 < V)]
    exact ⟨by simpa only [one_mul] using hb.2.1,hb.2.2⟩

theorem markedRootPartitionRootSet_eq_filter {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) {U V : ℝ}
    (hU : 1 < U) (hV : 1 < V) (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N) :
    (fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true).filter
        (fun p => markedRootNormalizedPoint U V p ∈ markedRootPartitionCell N i) =
      markedRootPartitionRootSet g₀ U V N i := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  ext p
  rcases p with ⟨u,c,v⟩
  rw [Finset.mem_filter]
  have hAu := markedRootPartitionInterval_integer_iff N (15*N) i.2.1 1 U hUp u
  have hBv := markedRootPartitionInterval_integer_iff N N i.2.2 1 V hVp v
  have hUg (hu : (u:ℝ)/U ∈ markedRootPartitionInterval N (15*N) i.2.1 1) :
      u ∈ realIntervalIntegers U (16*U) true true := by
    have hc := markedRootPartitionInterval_closed N (15*N) i.2.1 1 hu
    have hb := markedRootGrid_interval_bounds N 15 i.2.1 hN i.2.1.isLt 1 ((u:ℝ)/U) hc
    rw [fixedURoot_mem_closed_interval]
    exact ⟨by have h := (le_div_iff₀ hUp).mp hb.1; simpa only [one_mul] using h,
      by have h := (div_le_iff₀ hUp).mp hb.2; norm_num at h; exact h⟩
  have hVg (hv : (v:ℝ)/V ∈ markedRootPartitionInterval N N i.2.2 1) :
      v ∈ realIntervalIntegers V (2*V) true true := by
    have hc := markedRootPartitionInterval_closed N N i.2.2 1 hv
    have hb := markedRootGrid_interval_bounds N 1 i.2.2 hN (by simpa only [one_mul] using i.2.2.isLt) 1 ((v:ℝ)/V) hc
    rw [fixedURoot_mem_closed_interval]
    exact ⟨by have h := (le_div_iff₀ hVp).mp hb.1; simpa only [one_mul] using h,
      by have h := (div_le_iff₀ hVp).mp hb.2; norm_num at h; exact h⟩
  by_cases hup : 0 < (u:ℝ)
  · have huZ : 0 < u := by exact_mod_cast hup
    have hun : (u.natAbs:ℝ) = (u:ℝ) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_pos huZ]
    have hCr : c ∈ realIntervalIntegers ((u.natAbs:ℝ)*((i.1:ℝ)/N))
        ((u.natAbs:ℝ)*(((i.1:ℝ)+1)/N)) true (decide (i.1.val+1=N)) ↔
        (c:ℝ)/(u:ℝ) ∈ markedRootPartitionInterval N N i.1 0 := by
      simpa only [zero_add,hun] using markedRootPartitionInterval_integer_iff N N i.1 0
        (u.natAbs:ℝ) (by rw [hun]; exact hup) c
    have hCg (hr : (c:ℝ)/(u:ℝ) ∈ markedRootPartitionInterval N N i.1 0) :
        c ∈ realIntervalIntegers ((u.natAbs:ℝ)*0) ((u.natAbs:ℝ)*1) true true := by
      have hc := markedRootPartitionInterval_closed N N i.1 0 hr
      have hb := markedRootGrid_interval_bounds N 1 i.1 hN (by simpa only [one_mul] using i.1.isLt) 0
        ((c:ℝ)/(u:ℝ)) hc
      rw [fixedURoot_mem_closed_interval]
      simp only [hun,mul_zero,mul_one]
      exact ⟨by have h := (le_div_iff₀ hup).mp hb.1; simpa only [zero_mul] using h,
        by have h := (div_le_iff₀ hup).mp hb.2; norm_num at h; exact_mod_cast h⟩
    simp only [markedRootPartitionRootSet,fixedURootMatrixBoxPoints,fixedURootBoxPoints,
      Finset.mem_sigma,fixedURootBoxIndices,fixedURootPairs,Finset.mem_filter,
      Finset.product_eq_sprod,Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨_,hum⟩,⟨⟨_,_⟩,hmods⟩⟩,hp⟩
      exact ⟨⟨hAu.mpr hp.2.1,hum⟩,⟨⟨hCr.mpr hp.1,hBv.mpr hp.2.2⟩,hmods⟩⟩
    · rintro ⟨⟨hu,hum⟩,⟨⟨hc,hv⟩,hmods⟩⟩
      have hur := hAu.mp hu
      have hvr := hBv.mp hv
      have hrr := hCr.mp hc
      exact ⟨⟨⟨hUg hur,hum⟩,⟨⟨hCg hrr,hVg hvr⟩,hmods⟩⟩,hrr,hur,hvr⟩
  · have hg : (⟨u,c,v⟩ : Σ _u : ℤ,ℤ × ℤ) ∉
        fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true := by
      intro hp
      have hb := (fixedURootMatrixBox_coordinate_bounds g₀ U (16*U) 0 1 V (2*V) true true ⟨u,c,v⟩ hp).1.1
      linarith
    have hp : (⟨u,c,v⟩ : Σ _u : ℤ,ℤ × ℤ) ∉ markedRootPartitionRootSet g₀ U V N i := by
      intro hp
      simp only [markedRootPartitionRootSet,fixedURootMatrixBoxPoints,fixedURootBoxPoints,
        Finset.mem_sigma,fixedURootBoxIndices,fixedURootPairs,Finset.mem_filter,
        Finset.product_eq_sprod,Finset.mem_product] at hp
      have hu := (fixedURoot_mem_closed_interval U (16*U) u).mp (hUg (hAu.mp hp.1.1))
      linarith [hu.1]
    simp only [hg,hp,false_and]

theorem markedRootPartitionRootSet_sum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) {U V : ℝ}
    (hU : 1 < U) (hV : 1 < V) (N : ℕ) (hN : 0 < N) (f : (Σ _u : ℤ,ℤ × ℤ) → ℂ) :
    (∑ p ∈ fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true,f p) =
      ∑ i : MarkedRootGridIndex N,∑ p ∈ markedRootPartitionRootSet g₀ U V N i,f p := by
  rw [markedRootPartitionCell_finite_sum N hN _ (markedRootNormalizedPoint U V) f
    (fun p hp => markedRootNormalizedPoint_mem_domain g₀ hU hV p hp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [markedRootPartitionRootSet_eq_filter g₀ hU hV N hN i]

end ArtinMatthews
