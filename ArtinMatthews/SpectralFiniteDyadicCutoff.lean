module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
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

/-! A finite nonnegative spectral window sum can be covered by dyadic
bands with the exact geometric-series dependence on the cutoff. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_sum_geometric_le_two_last {b : ℝ} (hb : 2 ≤ b) (K : ℕ) :
    (∑ k ∈ Finset.range (K+1), b^k) ≤ 2*b^K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ,pow_succ]
    have hp : 0 ≤ b^K := pow_nonneg (by linarith) _
    have h := mul_le_mul_of_nonneg_right hb hp
    calc
      _ ≤ 2*b^K+b^K*b := add_le_add ih le_rfl
      _ ≤ b^K*b+b^K*b := add_le_add (by simpa only [mul_comm b] using h) le_rfl
      _ = _ := by ring

theorem spectral_nonneg_dyadic_cutoff_sum_le {ι : Type*} (u : Finset ι) (τ f : ι → ℝ)
    {R B C A : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hτ : ∀ i ∈ u, 1 ≤ τ i ∧ τ i ≤ R) (hf : ∀ i ∈ u, 0 ≤ f i)
    (hWin : ∀ k : ℕ, (∑ i ∈ u.filter (fun i => (2 : ℝ)^k ≤ τ i ∧ τ i ≤ 2*(2 : ℝ)^k), f i) ≤
      C*(((2 : ℝ)^k)^2+B*(2 : ℝ)^k)*A) :
    (∑ i ∈ u, f i) ≤ 2*C*(R^2+B*R)*A := by
  classical
  let M := ⌊R⌋₊
  let K := Nat.log 2 M
  let T (k : ℕ) : ℝ := 2^k
  let W (k : ℕ) (i : ι) := if T k ≤ τ i ∧ τ i ≤ 2*T k then f i else 0
  have hM : 1 ≤ M := (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).mpr (by exact_mod_cast hR)
  have hTK : T K ≤ R := by
    have h := Nat.pow_log_le_self 2 (show M ≠ 0 by omega)
    have hm : (T K) ≤ (M : ℝ) := by dsimp only [T,K]; exact_mod_cast h
    exact hm.trans (Nat.floor_le (zero_le_one.trans hR))
  have hcover (i : ι) (hi : i ∈ u) :
      ∃ k ∈ Finset.range (K+1), T k ≤ τ i ∧ τ i ≤ 2*T k := by
    let m := ⌊τ i⌋₊
    let k := Nat.log 2 m
    have hm : 1 ≤ m := (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).mpr
      (by exact_mod_cast (hτ i hi).1)
    have h₀ : m ≤ M := Nat.floor_le_floor (hτ i hi).2
    have hk : k ≤ K := Nat.log_mono_right h₀
    refine ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_le hk),?_,?_⟩
    · have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
      have hp : T k ≤ (m : ℝ) := by dsimp only [T,k]; exact_mod_cast h
      exact hp.trans (Nat.floor_le (zero_le_one.trans (hτ i hi).1))
    · have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) m
      have he : (m : ℝ)+1 ≤ (2:ℝ)^(k+1) := by
        exact_mod_cast (Nat.succ_le_of_lt h)
      rw [pow_succ,mul_comm ((2:ℝ)^k)] at he
      exact (Nat.lt_floor_add_one (τ i)).le.trans he
  have hE :
      (∑ i ∈ u, f i) ≤
        ∑ k ∈ Finset.range (K+1), ∑ i ∈ u.filter (fun i => T k ≤ τ i ∧ τ i ≤ 2*T k), f i := by
    calc
      _ ≤ ∑ i ∈ u, ∑ k ∈ Finset.range (K+1), W k i := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k,hk,he⟩ := hcover i hi
        have h := Finset.single_le_sum (f := fun j => W j i)
          (fun j _ => by
            unfold W
            split_ifs
            · exact hf i hi
            · exact le_rfl) hk
        simpa only [W,ite_eq_left he] using h
      _ = _ := by rw [Finset.sum_comm]; simp only [W,Finset.sum_filter]
  have hT₂ (k : ℕ) : (T k)^2 = (4 : ℝ)^k := by
    dsimp only [T]
    rw [sq,← mul_pow]
    norm_num
  have hSumOne : (∑ k ∈ Finset.range (K+1), T k) ≤ 2*R :=
    (spectral_sum_geometric_le_two_last (by norm_num : (2:ℝ)≤2) K).trans
      (mul_le_mul_of_nonneg_left hTK (by norm_num))
  have hSumTwo : (∑ k ∈ Finset.range (K+1), (T k)^2) ≤ 2*R^2 := by
    simp only [hT₂]
    refine (spectral_sum_geometric_le_two_last (by norm_num : (2:ℝ)≤4) K).trans ?_
    rw [← hT₂]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by dsimp only [T]; positivity) hTK 2)
      (by norm_num)
  calc
    _ ≤ _ := hE
    _ ≤ ∑ k ∈ Finset.range (K+1), C*((T k)^2+B*T k)*A :=
      Finset.sum_le_sum (fun k _ => hWin k)
    _ = C*((∑ k ∈ Finset.range (K+1), (T k)^2)+B*(∑ k ∈ Finset.range (K+1), T k))*A := by
      rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ C*(2*R^2+B*(2*R))*A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add hSumTwo (mul_le_mul_of_nonneg_left hSumOne hB)) hC) hA
    _ = _ := by ring

end ArtinMatthews
