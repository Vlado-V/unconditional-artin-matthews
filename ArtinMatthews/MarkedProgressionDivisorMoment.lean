module

public import ArtinMatthews.MarkedProgressionLargestFactor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ArtinMatthews.MarkedProgressionCounting
public import Mathlib.NumberTheory.Harmonic.Bounds
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


set_option backward.privateInPublic true
@[expose] public section

/-! The squared divisor count on the residue class one, with the same
finite integer range in the divisor and four-factor sums. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem markedProgression_last_factor_count {a X D : ℕ}
    (ha : 0 < a) (hD : 0 < D) (hAD : a*D ≤ X) :
    ((markedProgressionLastFactors a X D).card : ℝ) ≤
      (2*(X:ℝ)/a)*(D:ℝ)⁻¹ := by
  classical
  by_cases h : (markedProgressionLastFactors a X D).Nonempty
  · obtain ⟨r₀,hr₀⟩ := h
    have hm₀ := (mem_filter.mp hr₀).2
    have hcop : a.Coprime D := (Nat.coprime_of_mul_modEq_one r₀ hm₀).symm
    have heq : markedProgressionLastFactors a X D =
        (Ioc 0 (X/D)).filter (fun r => Nat.ModEq a r r₀) := by
      ext r
      simp only [markedProgressionLastFactors,mem_filter]
      exact and_congr_right (fun _ => ⟨
        fun hr => Nat.ModEq.cancel_left_of_coprime hcop (hr.trans hm₀.symm),
        fun hr => (hr.mul_left D).trans hm₀⟩)
    have hcount : ((markedProgressionLastFactors a X D).card : ℝ) ≤
        ((X/D:ℕ):ℝ)/a+1 := by
      rw [heq]
      have he := (abs_le.mp (marked_interval_residue_error 0 (X/D) a r₀ (Nat.zero_le _) ha)).2
      simp only [Nat.cast_zero,sub_zero] at he
      linarith
    have ha' : 0 < (a:ℝ) := by exact_mod_cast ha
    have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
    have hone : 1 ≤ (X:ℝ)/((D:ℝ)*a) := by
      apply (le_div_iff₀ (mul_pos hD' ha')).mpr
      rw [one_mul,mul_comm]
      exact_mod_cast hAD
    calc
      _ ≤ ((X/D:ℕ):ℝ)/a+1 := hcount
      _ ≤ ((X:ℝ)/D)/a+1 := add_le_add (div_le_div_of_nonneg_right
        (Nat.cast_div_le : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D) ha'.le) le_rfl
      _ ≤ 2*((X:ℝ)/((D:ℝ)*a)) := by rw [div_div]; linarith
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp h,card_empty,Nat.cast_zero]
    positivity

theorem markedProgression_short_triple_modulus {a X D : ℕ}
    (ha : a^4 ≤ X) (hD : D^4 ≤ X^3) : a*D ≤ X := by
  apply (Nat.pow_le_pow_iff_left (show (4:ℕ) ≠ 0 by decide)).mp
  calc
    (a*D)^4 = a^4*D^4 := mul_pow _ _ _
    _ ≤ X*X^3 := Nat.mul_le_mul ha hD
    _ = X^4 := by ring

private theorem markedProgression_short_triple_product_pos {X : ℕ}
    {t : MarkedDivisorTriple} (ht : t ∈ markedProgressionShortTriples X) :
    0 < markedDivisorTripleProduct t := by
  obtain ⟨ha,hb,hc⟩ : t.1 ∈ Ioc 0 X ∧ t.2.1 ∈ Ioc 0 X ∧ t.2.2 ∈ Ioc 0 X := by
    simpa only [markedDivisorTripleBox,product_eq_sprod,mem_product] using (mem_filter.mp ht).1
  exact Nat.mul_pos (Nat.mul_pos (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1) (mem_Ioc.mp hc).1

theorem markedProgression_short_triple_harmonic (X : ℕ) :
    (∑ t ∈ markedProgressionShortTriples X, (markedDivisorTripleProduct t:ℝ)⁻¹) ≤
      (1+Real.log (X:ℝ))^3 := by
  let S := Ioc 0 X
  let w (i : ℕ) := (i:ℝ)⁻¹
  have hsum : (∑ i ∈ S, w i) ≤ 1+Real.log (X:ℝ) := by
    have hS : S = Icc 1 X := by
      ext i
      simp only [S,mem_Ioc,mem_Icc]
      omega
    rw [hS]
    simpa only [w,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
      harmonic_le_one_add_log X
  calc
    _ ≤ ∑ t ∈ markedDivisorTripleBox X, (markedDivisorTripleProduct t:ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (∑ i ∈ S, w i)^3 := by
      change (∑ t ∈ S.product (S.product S), (markedDivisorTripleProduct t:ℝ)⁻¹) = _
      simp only [product_eq_sprod,sum_product,markedDivisorTripleProduct,Nat.cast_mul,mul_inv_rev]
      simp only [pow_succ,pow_zero,one_mul,sum_mul,mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro c _
      dsimp only [w]
      ring
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hsum 3

theorem marked_progression_divisor_square_le {a X : ℕ} (ha : 0 < a) (haX : a^4 ≤ X) :
    (∑ n ∈ (Icc 1 X).filter (fun n => Nat.ModEq a n 1), (n.divisors.card:ℝ)^2) ≤
      8*(X:ℝ)/a*(1+Real.log (X:ℝ))^3 := by
  have hinterval : Icc 1 X = Ioc 0 X := by
    ext n
    simp only [mem_Icc,mem_Ioc]
    omega
  rw [hinterval]
  change (∑ n ∈ markedProgressionDivisorIntegers a X, (n.divisors.card:ℝ)^2) ≤ _
  let S := markedProgressionShortTriples X
  let D := markedDivisorTripleProduct
  let W := 2*(X:ℝ)/a
  calc
    _ ≤ 4 * ∑ t ∈ S, ((markedProgressionLastFactors a X (D t)).card:ℝ) := by
      exact_mod_cast (markedProgression_divisor_pair_count a X).trans
        (markedProgression_quadruple_count a X)
    _ ≤ 4 * ∑ t ∈ S, W*(D t:ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left (sum_le_sum ?_) (by norm_num)
      intro t ht
      exact markedProgression_last_factor_count ha (markedProgression_short_triple_product_pos ht)
        (markedProgression_short_triple_modulus haX (mem_filter.mp ht).2)
    _ = (4*W) * ∑ t ∈ S, (D t:ℝ)⁻¹ := by rw [← mul_sum,mul_assoc]
    _ ≤ (4*W) * (1+Real.log (X:ℝ))^3 :=
      mul_le_mul_of_nonneg_left (markedProgression_short_triple_harmonic X) (by dsimp [W]; positivity)
    _ = _ := by dsimp only [W]; ring

/-- The original quotients can be any finite set whose represented
integers lie in the interval. The quotient zero is included. -/
theorem marked_progression_shifted_divisor_square_le {a X : ℕ} (ha : 0 < a) (haX : a^4 ≤ X)
    (H : Finset ℕ) (hH : ∀ h ∈ H, 1+a*h ≤ X) :
    (∑ h ∈ H, ((1+a*h).divisors.card:ℝ)^2) ≤
      8*(X:ℝ)/a*(1+Real.log (X:ℝ))^3 := by
  let f (h : ℕ) := 1+a*h
  have hfi : Function.Injective f := fun _ _ h =>
    Nat.eq_of_mul_eq_mul_left ha (Nat.add_left_cancel h)
  calc
    _ = ∑ n ∈ H.image f, (n.divisors.card:ℝ)^2 := (sum_image hfi.injOn).symm
    _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => Nat.ModEq a n 1), (n.divisors.card:ℝ)^2 := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
      intro n hn
      obtain ⟨h,hh,rfl⟩ := mem_image.mp hn
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp [f]; omega,hH h hh⟩,?_⟩
      have hm : Nat.ModEq a (a*h) 0 := Nat.modEq_zero_iff_dvd.mpr ⟨h,rfl⟩
      simpa only [f,add_zero] using hm.add_left 1
    _ ≤ _ := marked_progression_divisor_square_le ha haX

end ArtinMatthews
