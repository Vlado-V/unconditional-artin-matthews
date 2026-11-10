module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
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

/-! A finite divisor decomposition for the square-root gcd weight
appearing in a same-cusp diagonal Weil sum. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_sum_inv_sqrt_succ_le (L : ℕ) :
    (∑ k ∈ Finset.range L, (Real.sqrt ((k+1 : ℕ) : ℝ))⁻¹) ≤ 2*Real.sqrt (L : ℝ) := by
  induction L with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < Real.sqrt ((k+1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hstep : (Real.sqrt ((k+1 : ℕ) : ℝ))⁻¹ ≤
        2*(Real.sqrt ((k+1 : ℕ) : ℝ)-Real.sqrt (k : ℝ)) := by
      rw [← one_div]
      apply (div_le_iff₀ hpos).mpr
      have hs := Real.sq_sqrt (show 0 ≤ ((k+1 : ℕ) : ℝ) by positivity)
      have ht := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have he : ((k+1 : ℕ) : ℝ) = (k : ℝ)+1 := by push_cast; rfl
      nlinarith only [hs,ht,he,sq_nonneg (Real.sqrt ((k+1 : ℕ) : ℝ)-Real.sqrt (k : ℝ))]
    rw [Finset.sum_range_succ]
    change _ ≤ 2*Real.sqrt ((k+1 : ℕ) : ℝ)
    linarith only [ih,hstep]

theorem spectral_sum_inv_sqrt_multiple_quotient_le (d L : ℕ) :
    (∑ k ∈ (Finset.range L).filter (fun k => d ∣ k+1),
      (Real.sqrt (((k+1)/d : ℕ) : ℝ))⁻¹) ≤ 2*Real.sqrt (L : ℝ) := by
  let S := (Finset.range L).filter (fun k => d ∣ k+1)
  let f (k : ℕ) := (k+1)/d-1
  have hq (k : ℕ) (hk : k ∈ S) : 1 ≤ (k+1)/d := by
    have h := Nat.div_mul_cancel (Finset.mem_filter.mp hk).2
    by_contra hn
    have hz : (k+1)/d = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz,zero_mul] at h
    omega
  have hinj : (S : Set ℕ).InjOn f := by
    intro i hi j hj he
    have h₁ := Nat.div_mul_cancel (Finset.mem_filter.mp hi).2
    have h₂ := Nat.div_mul_cancel (Finset.mem_filter.mp hj).2
    have h₃ := hq i hi
    have h₄ := hq j hj
    dsimp only [f] at he
    have h₅ : (i+1)/d = (j+1)/d := by omega
    rw [h₅,h₂] at h₁
    omega
  have hmap : S.image f ⊆ Finset.range (L/d) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have h₁ := hq k hk
    have h₂ : (k+1)/d ≤ L/d :=
      Nat.div_le_div_right (by
        have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
        omega)
    apply Finset.mem_range.mpr
    dsimp only [f]
    omega
  have hpoint (k : ℕ) (hk : k ∈ S) :
      (Real.sqrt (((k+1)/d : ℕ) : ℝ))⁻¹ ≤ (Real.sqrt ((f k+1 : ℕ) : ℝ))⁻¹ := by
    rw [show f k+1 = (k+1)/d from Nat.sub_add_cancel (hq k hk)]
  calc
    _ ≤ ∑ j ∈ Finset.range (L/d), (Real.sqrt ((j+1 : ℕ) : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_injOn f hinj hmap hpoint (fun _ _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ 2*Real.sqrt ((L/d : ℕ) : ℝ) := spectral_sum_inv_sqrt_succ_le (L/d)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.div_le_self L d)))
      (by norm_num)

theorem spectral_sum_sqrt_gcd_div_sqrt_le (n L : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range L,
      Real.sqrt (Nat.gcd (k+1) n : ℝ)/Real.sqrt ((k+1 : ℕ) : ℝ)) ≤
      2*Real.sqrt (L : ℝ)*(n.divisors.card : ℝ) := by
  let W (d k : ℕ) : ℝ := if d ∣ k+1 then (Real.sqrt (((k+1)/d : ℕ) : ℝ))⁻¹ else 0
  have hW (d k : ℕ) : 0 ≤ W d k := by unfold W; split_ifs <;> positivity
  have hpoint (k : ℕ) : Real.sqrt (Nat.gcd (k+1) n : ℝ)/Real.sqrt ((k+1 : ℕ) : ℝ) ≤
      ∑ d ∈ n.divisors, W d k := by
    let d := Nat.gcd (k+1) n
    have hd : 0 < d := Nat.gcd_pos_of_pos_left n (Nat.succ_pos k)
    have hdv : d ∣ k+1 := Nat.gcd_dvd_left (k+1) n
    have hdn : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right (k+1) n,hn.ne'⟩
    have hmul := Nat.div_mul_cancel hdv
    have hq : 0 < (k+1)/d := by
      by_contra hn'
      have he : (k+1)/d = 0 := Nat.eq_zero_of_not_pos hn'
      simp only [he,zero_mul] at hmul
      omega
    have hS : Real.sqrt ((k+1 : ℕ) : ℝ) = Real.sqrt (((k+1)/d : ℕ) : ℝ)*Real.sqrt (d : ℝ) := by
      rw [show ((k+1 : ℕ) : ℝ) = (((k+1)/d : ℕ) : ℝ)*(d : ℝ) by exact_mod_cast hmul.symm,
        Real.sqrt_mul (by positivity)]
    have he : Real.sqrt (d : ℝ)/Real.sqrt ((k+1 : ℕ) : ℝ) = W d k := by
      change _ = if d ∣ k+1 then (Real.sqrt (((k+1)/d : ℕ) : ℝ))⁻¹ else 0
      rw [hS,ite_eq_left hdv]
      have h₁ : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hd)
      have h₂ : 0 < Real.sqrt (((k+1)/d : ℕ) : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hq)
      field_simp [h₁.ne',h₂.ne']
    exact he.le.trans (Finset.single_le_sum (fun a _ => hW a k) hdn)
  calc
    _ ≤ ∑ k ∈ Finset.range L, ∑ d ∈ n.divisors, W d k :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = ∑ d ∈ n.divisors, ∑ k ∈ Finset.range L, W d k := Finset.sum_comm
    _ ≤ ∑ _d ∈ n.divisors, 2*Real.sqrt (L : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [W,← Finset.sum_filter] using spectral_sum_inv_sqrt_multiple_quotient_le d L
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]

end ArtinMatthews
