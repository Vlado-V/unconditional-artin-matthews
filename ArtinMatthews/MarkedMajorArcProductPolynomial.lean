module

public import ArtinMatthews.MarkedSparsePrimeMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDivisorPairs


set_option backward.privateInPublic true
@[expose] public section

/-! The actual product of two finite Dirichlet polynomials, grouped by
integer product. Its coefficient mass is proved by the divisor-square
estimate; no cancellation assumption is imposed on either factor. -/
namespace ArtinMatthews
open Finset OAI.TwoPointCorrelations MeasureTheory

noncomputable def markedNaturalPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n*markedPrimePhase n t

noncomputable def markedProductFiber (S T : Finset ℕ) (n : ℕ) : Finset (ℕ×ℕ) :=
  (S×ˢT).filter (fun v => v.1*v.2=n)

noncomputable def markedProductCoefficient (S T : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ v ∈ markedProductFiber S T n, a v.1*b v.2

lemma markedPrimePhase_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    markedPrimePhase m t*markedPrimePhase n t = markedPrimePhase (m*n) t := by
  unfold markedPrimePhase
  rw [← Complex.exp_add,Nat.cast_mul,Real.log_mul
    (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  congr 1
  push_cast
  ring

 theorem markedNaturalPolynomial_product (S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ n ∈ T, 0 < n)
    (hbound : ∀ m ∈ S, ∀ n ∈ T, m*n ≤ N) (t : ℝ) :
    markedNaturalPolynomial S a t*markedNaturalPolynomial T b t =
      markedNaturalPolynomial (Icc 1 N) (markedProductCoefficient S T a b) t := by
  classical
  have hmap : ∀ v ∈ S×ˢT, v.1*v.2 ∈ Icc 1 N := by
    intro v hv
    obtain ⟨hm,hn⟩ := mem_product.mp hv
    exact mem_Icc.mpr ⟨Nat.mul_pos (hS _ hm) (hT _ hn),hbound _ hm _ hn⟩
  have hf := sum_fiberwise_of_maps_to hmap
    (fun v : ℕ×ℕ => (a v.1*b v.2)*markedPrimePhase (v.1*v.2) t)
  have he : markedNaturalPolynomial (Icc 1 N) (markedProductCoefficient S T a b) t =
      ∑ v ∈ S×ˢT, (a v.1*b v.2)*markedPrimePhase (v.1*v.2) t := by
    rw [← hf]
    unfold markedNaturalPolynomial markedProductCoefficient markedProductFiber
    apply sum_congr rfl
    intro n _
    rw [sum_mul]
    apply sum_congr rfl
    intro v hv
    rw [(mem_filter.mp hv).2]
  rw [he]
  unfold markedNaturalPolynomial
  rw [sum_mul,sum_product]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [← markedPrimePhase_mul (hS _ hm) (hT _ hn)]
  ring

lemma markedProductFiber_card_le (S T : Finset ℕ) {n N : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    (markedProductFiber S T n).card ≤ ((Icc 1 N).filter (fun d => d∣n)).card := by
  classical
  apply card_le_card_of_injOn Prod.fst
  · intro v hv
    have he := (mem_filter.mp hv).2
    have hd : v.1∣n := ⟨v.2,he.symm⟩
    have hvpos : 0 < v.1 := by
      have : 0 < v.1*v.2 := by simpa only [he] using hn
      exact (Nat.pos_of_mul_pos_right this)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hvpos,(Nat.le_of_dvd hn hd).trans hnN⟩,hd⟩
  · intro v hv w hw he
    have hvn := (mem_filter.mp hv).2
    have hwn := (mem_filter.mp hw).2
    have hpos : 0 < v.1 := by
      have : 0 < v.1*v.2 := by simpa only [hvn] using hn
      exact (Nat.pos_of_mul_pos_right this)
    have he2 : v.2=w.2 := Nat.eq_of_mul_eq_mul_left hpos (by rw [hvn,he,hwn])
    exact Prod.ext he he2

 theorem markedProductCoefficient_square_mass (S T : Finset ℕ) (a b : ℕ → ℂ)
    (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A) (hb : ∀ n ∈ T, ‖b n‖ ≤ B) :
    (∑ n ∈ Icc 1 N, ‖markedProductCoefficient S T a b n‖^2) ≤
      (A*B)^2*(N:ℝ)*(∑ d ∈ Icc 1 N, 1/(d:ℝ))^3 := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      ‖markedProductCoefficient S T a b n‖ ≤
        A*B*(((Icc 1 N).filter (fun d => d∣n)).card:ℝ) := by
    calc
      _ ≤ ∑ v ∈ markedProductFiber S T n, ‖a v.1*b v.2‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ markedProductFiber S T n, A*B := by
        apply sum_le_sum
        intro v hv
        obtain ⟨hm,hn⟩ := mem_product.mp (mem_filter.mp hv).1
        rw [norm_mul]
        exact mul_le_mul (ha _ hm) (hb _ hn) (norm_nonneg _) hA
      _ = A*B*((markedProductFiber S T n).card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast markedProductFiber_card_le S T (mem_Icc.mp hn).1 (mem_Icc.mp hn).2)
        (mul_nonneg hA hB)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (A*B)^2*(((Icc 1 N).filter (fun d => d∣n)).card:ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpoint n hn) 2
    _ = (A*B)^2*∑ n ∈ Icc 1 N, (((Icc 1 N).filter (fun d => d∣n)).card:ℝ)^2 :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      have hh := mrt_divisor_count_second_moment (Icc 1 N)
        (fun d hd => (mem_Icc.mp hd).1)
        (fun d hd e he hed => mem_Icc.mpr ⟨he,
          (Nat.le_of_dvd (mem_Icc.mp hd).1 hed).trans (mem_Icc.mp hd).2⟩) N
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)

end ArtinMatthews
