module

public import ArtinMatthews.PrimeExtractionWeightUniform
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

/-! The product cutoff for the exact tuple expansion and the predecessor
cutoff for the rough sieve. The extra one is absorbed by the actual
support, retaining the literal n-1 in the test. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantExtraction_predecessor_reindex (T x : ℝ) (hT : 0 ≤ T) (hx : 1 ≤ x)
    (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℂ)
    (hz : ∀ n, T*x < ((n-1:ℕ):ℝ) → F n=0) :
    (∑ n∈(Ioc 0 ⌊(T+1)*x⌋₊).filter P,F n) =
      ∑ u∈(Icc 0 ⌊T*x⌋₊).filter (fun u => P (u+1)),F (u+1) := by
  let N := ⌊T*x⌋₊
  let S := (Ioc 0 (N+1)).filter P
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hTx : 0 ≤ T*x := mul_nonneg hT hx0
  have hTx1 : 0 ≤ (T+1)*x := mul_nonneg (by positivity) hx0
  have hN : N+1 ≤ ⌊(T+1)*x⌋₊ := by
    apply (Nat.le_floor_iff hTx1).mpr
    push_cast
    have h := Nat.floor_le hTx
    change (N:ℝ)≤T*x at h
    linarith
  have hsub : S ⊆ (Ioc 0 ⌊(T+1)*x⌋₊).filter P := by
    intro n hn
    obtain ⟨hn,hP⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hN⟩,hP⟩
  calc
    _ = ∑ n∈S,F n := by
      symm
      apply sum_subset hsub
      intro n hn hns
      obtain ⟨hn,hP⟩ := mem_filter.mp hn
      apply hz
      by_contra! hle
      have h : n-1≤N := (Nat.le_floor_iff hTx).mpr hle
      exact hns (mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,by omega⟩,hP⟩)
    _ = _ := by
      symm
      apply Finset.sum_bij (fun u _ => u+1)
      · intro u hu
        obtain ⟨hu,hP⟩ := mem_filter.mp hu
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,Nat.succ_le_succ (mem_Icc.mp hu).2⟩,hP⟩
      · intro u _ v _ huv
        exact Nat.add_right_cancel huv
      · intro n hn
        obtain ⟨hn,hP⟩ := mem_filter.mp hn
        have hn0 := (mem_Ioc.mp hn).1
        have hn1 := (mem_Ioc.mp hn).2
        refine ⟨n-1,mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,?_⟩,by omega⟩
        rwa [Nat.sub_add_cancel (by omega : 1≤n)]
      · intro _ _
        rfl

theorem markedExtractionWeight_eq_zero_of_past {J : Type*} [Fintype J]
    (e : J → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {T x : ℝ} (hx : 0<x)
    (hhigh : ∀ t, T<t → Φ t=0) {n : ℕ} (hn : T*x<((n-1:ℕ):ℝ)) :
    markedExtractionWeight e G Φ x n=0 := by
  rw [markedExtractionWeight,hhigh _ ((lt_div_iff₀ hx).mpr hn),Complex.ofReal_zero,zero_mul,zero_mul]

end
end ArtinMatthews
