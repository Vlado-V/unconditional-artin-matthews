module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted comparison mass on the positive multiples of a prime
label dividing the actual displacement. Two finite Cauchy–Schwarz steps
use the fourth moments on the literal endpoint intervals. -/

namespace ArtinMatthews
open Finset Set
open scoped BigOperators
noncomputable section

def sourceComparisonPrimeHitRows (N d p : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (fun w => p ∣ w ∨ p ∣ w + d)

theorem sourceComparisonPrimeHitRows_card (N d p : ℕ) (hp : 0 < p) (hpd : p ∣ d) :
    (sourceComparisonPrimeHitRows N d p).card = N / p := by
  let e : ℕ ↪ ℕ := ⟨fun k => p * k, fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h⟩
  have he : sourceComparisonPrimeHitRows N d p = (Finset.Ioc 0 (N / p)).map e := by
    ext w
    rw [sourceComparisonPrimeHitRows, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_map,
      Nat.dvd_add_left hpd, or_self]
    constructor
    · rintro ⟨⟨hw, hN⟩, k, rfl⟩
      have hk : 0 < k := by
        by_contra hn
        rw [Nat.eq_zero_of_not_pos hn, mul_zero] at hw
        omega
      exact ⟨k, Finset.mem_Ioc.mpr ⟨hk, (Nat.le_div_iff_mul_le hp).2 (by simpa only [Nat.mul_comm k p] using hN)⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hk₀, hkN⟩ := Finset.mem_Ioc.mp hk
      change (0 < p * k ∧ p * k ≤ N) ∧ p ∣ p * k
      exact ⟨⟨Nat.mul_pos hp hk₀, (by simpa only [Nat.mul_comm k p] using (Nat.le_div_iff_mul_le hp).1 hkN)⟩, dvd_mul_right p k⟩
  rw [he, Finset.card_map, Nat.card_Ioc, Nat.sub_zero]

def sourceComparisonFourthMass (N : ℕ) (U : ℕ → ℂ) : ℝ :=
  ∑ w ∈ Finset.Ioc 0 N, ‖U w‖ ^ 4

def sourceComparisonFreeHitWeight (Ψ : ℝ → ℂ) (U V : ℕ → ℂ) (Y : ℝ) (d w : ℕ) : ℝ :=
  ‖Ψ ((w : ℝ) / Y)‖ / (w : ℝ) * ‖U w‖ * ‖V (w + d)‖

theorem sourceComparisonFreeHitWeight_nonneg (Ψ : ℝ → ℂ) (U V : ℕ → ℂ) (Y : ℝ) (d w : ℕ) :
    0 ≤ sourceComparisonFreeHitWeight Ψ U V Y d w := by
  unfold sourceComparisonFreeHitWeight
  positivity

private theorem sqrt_sqrt_rpow {A : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (Real.sqrt A) = A ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
  norm_num

theorem sourceComparison_sum_mul_le_fourth {ι : Type*} (T : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ T, f i * g i) ≤ Real.sqrt (T.card : ℝ) *
      (∑ i ∈ T, f i ^ 4) ^ (1 / 4 : ℝ) * (∑ i ∈ T, g i ^ 4) ^ (1 / 4 : ℝ) := by
  have hf : 0 ≤ ∑ i ∈ T, f i ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hg : 0 ≤ ∑ i ∈ T, g i ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have h₂ : (∑ i ∈ T, (f i * g i) ^ 2) ≤
      Real.sqrt (∑ i ∈ T, f i ^ 4) * Real.sqrt (∑ i ∈ T, g i ^ 4) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt T (fun i => f i ^ (2 : ℕ))
      (fun i => g i ^ (2 : ℕ))
    change (∑ i ∈ T, f i ^ (2 : ℕ) * g i ^ (2 : ℕ)) ≤
      Real.sqrt (∑ i ∈ T, (f i ^ (2 : ℕ)) ^ (2 : ℕ)) *
        Real.sqrt (∑ i ∈ T, (g i ^ (2 : ℕ)) ^ (2 : ℕ)) at h
    simpa only [mul_pow, ← pow_mul, Nat.reduceMul] using h
  calc
    _ ≤ Real.sqrt (T.card : ℝ) * Real.sqrt (∑ i ∈ T, (f i * g i) ^ 2) := by
      simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
        Real.sum_mul_le_sqrt_mul_sqrt T (fun _ => (1 : ℝ)) (fun i => f i * g i)
    _ ≤ Real.sqrt (T.card : ℝ) * Real.sqrt
        (Real.sqrt (∑ i ∈ T, f i ^ 4) * Real.sqrt (∑ i ∈ T, g i ^ 4)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _), sqrt_sqrt_rpow hf, sqrt_sqrt_rpow hg, mul_assoc]

private theorem freeHit_scale {Y a b B : ℝ} (hY : 0 < Y) (hb : 0 ≤ b) {p : ℕ} :
    B / (a * Y) * Real.sqrt (b * Y / (p : ℝ)) =
      (B * Real.sqrt b / a) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Y ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  have hdiv : Real.sqrt Y / Y = (Real.sqrt Y)⁻¹ := (div_eq_iff hY.ne').2 (by
    calc
      _ = (Real.sqrt Y)⁻¹ * (Real.sqrt Y * Real.sqrt Y) := by
        rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
      _ = _ := by rw [← pow_two, Real.sq_sqrt hY.le])
  rw [Real.sqrt_div (mul_nonneg hb hY.le), Real.sqrt_mul hb,
    Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_neg hY.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc
    _ = B * Real.sqrt b / a * (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt Y / Y) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hdiv]

theorem sourceComparison_freeHit_le (Ψ : ℝ → ℂ) (U V : ℕ → ℂ)
    {Y a b B : ℝ} (hY : 0 < Y) (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ x ∉ Set.Icc a b, Ψ x = 0) (hB : ∀ x, ‖Ψ x‖ ≤ B)
    (d p : ℕ) (hp : 0 < p) (hpd : p ∣ d) :
    (∑ w ∈ sourceComparisonPrimeHitRows ⌊b * Y⌋₊ d p, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤
      (B * Real.sqrt b / a) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Y ^ (-(1 / 2 : ℝ)) *
        (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
        (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ) := by
  let N := ⌊b * Y⌋₊
  let R := sourceComparisonPrimeHitRows N d p
  let A := B / (a * Y)
  let f (w : ℕ) := ‖U w‖
  let g (w : ℕ) := ‖V (w + d)‖
  let M₁ := sourceComparisonFourthMass N U
  let M₂ := sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V
  have hB₀ : 0 ≤ B := (norm_nonneg (Ψ 0)).trans (hB 0)
  have hA : 0 ≤ A := div_nonneg hB₀ (mul_nonneg ha.le hY.le)
  have hby : 0 ≤ b * Y := mul_nonneg hb hY.le
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hsub : R ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hcard : (R.card : ℝ) ≤ b * Y / (p : ℝ) := by
    rw [show R.card = N / p from sourceComparisonPrimeHitRows_card N d p hp hpd]
    apply (le_div_iff₀ hp').2
    exact (show ((N / p : ℕ) : ℝ) * (p : ℝ) ≤ (N : ℝ) by
      exact_mod_cast Nat.div_mul_le_self N p).trans (Nat.floor_le hby)
  have hfirst : (∑ w ∈ R, f w ^ 4) ≤ M₁ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hsecond : (∑ w ∈ R, g w ^ 4) ≤ M₂ := by
    let e : ℕ ↪ ℕ := ⟨fun w => w + d, fun _ _ h => Nat.add_right_cancel h⟩
    have hmap : R.map e ⊆ Finset.Ioc 0 (N + d) := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨hw₀, hwN⟩ := Finset.mem_Ioc.mp (hsub hw)
      exact Finset.mem_Ioc.mpr ⟨by change 0 < w + d; omega, Nat.add_le_add_right hwN d⟩
    change (∑ w ∈ R, ‖V (w + d)‖ ^ 4) ≤ sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V
    rw [Nat.floor_add_natCast hby]
    calc
      _ = ∑ y ∈ R.map e, ‖V y‖ ^ 4 := (Finset.sum_map R e (fun y => ‖V y‖ ^ 4)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ => by positivity)
  have hA₀ (w : ℕ) (hw : w ∈ R) : ‖Ψ ((w : ℝ) / Y)‖ / (w : ℝ) ≤ A := by
    have hw' : 0 < (w : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp (hsub hw)).1
    by_cases h : (w : ℝ) / Y ∈ Set.Icc a b
    · have hwY := (le_div_iff₀ hY).1 h.1
      exact (div_le_div_of_nonneg_right (hB _) hw'.le).trans
        (div_le_div_of_nonneg_left hB₀ (mul_pos ha hY) hwY)
    · rw [hΨ _ h, norm_zero, zero_div]
      exact hA
  have hF : 0 ≤ ∑ w ∈ R, f w ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hG : 0 ≤ ∑ w ∈ R, g w ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hF' := Real.rpow_le_rpow hF hfirst (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hG' := Real.rpow_le_rpow hG hsecond (by norm_num : 0 ≤ (1 / 4 : ℝ))
  change (∑ w ∈ R, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤ _
  calc
    _ ≤ ∑ w ∈ R, A * (f w * g w) := by
      apply Finset.sum_le_sum
      intro w hw
      unfold sourceComparisonFreeHitWeight
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hA₀ w hw) (by positivity)
    _ = A * ∑ w ∈ R, f w * g w := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (Real.sqrt (R.card : ℝ) * (∑ w ∈ R, f w ^ 4) ^ (1 / 4 : ℝ) *
        (∑ w ∈ R, g w ^ 4) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceComparison_sum_mul_le_fourth R f g) hA
    _ ≤ A * (Real.sqrt (b * Y / (p : ℝ)) * M₁ ^ (1 / 4 : ℝ) * M₂ ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact mul_le_mul (mul_le_mul (Real.sqrt_le_sqrt hcard) hF'
        (Real.rpow_nonneg hF _) (Real.sqrt_nonneg _)) hG' (Real.rpow_nonneg hG _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hF.trans hfirst) _))
    _ = _ := by
      change (B / (a * Y)) * (_ * M₁ ^ (1 / 4 : ℝ) * M₂ ^ (1 / 4 : ℝ)) = _
      rw [← mul_assoc, ← mul_assoc, freeHit_scale hY hb]

theorem sourceComparison_freeHit_le_of_subset (Ψ : ℝ → ℂ) (U V : ℕ → ℂ)
    {Y a b B : ℝ} (hY : 0 < Y) (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ x ∉ Set.Icc a b, Ψ x = 0) (hB : ∀ x, ‖Ψ x‖ ≤ B)
    (d p : ℕ) (hp : 0 < p) (hpd : p ∣ d) {T : Finset ℕ} (hT : T ⊆ Finset.Ioc 0 ⌊b * Y⌋₊) :
    (∑ w ∈ T.filter (fun w => p ∣ w ∨ p ∣ w + d), sourceComparisonFreeHitWeight Ψ U V Y d w) ≤
      (B * Real.sqrt b / a) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Y ^ (-(1 / 2 : ℝ)) *
        (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
        (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ) :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hT)
    (fun w _ _ => sourceComparisonFreeHitWeight_nonneg Ψ U V Y d w)).trans
    (sourceComparison_freeHit_le Ψ U V hY ha hb hΨ hB d p hp hpd)

end
end ArtinMatthews
