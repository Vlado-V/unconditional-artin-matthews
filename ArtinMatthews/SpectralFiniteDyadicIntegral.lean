module

public import ArtinMatthews.SpectralFiniteDyadicCutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-! A nonnegative density on a cutoff is bounded by the sum of the
actual dyadic window integrals. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace ArtinMatthews

theorem spectral_nonneg_dyadic_cutoff_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (τ f : α → ℝ) (hτ : Measurable τ) (hf : ∀ x, 0 ≤ f x)
    {R B C : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hWin : ∀ k : ℕ, IntegrableOn f (τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k)) μ ∧
      (∫ x in τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k), f x ∂μ) ≤
        C*(((2 : ℝ)^k)^2+B*(2 : ℝ)^k)) :
    IntegrableOn f (τ ⁻¹' Icc 1 R) μ ∧
      (∫ x in τ ⁻¹' Icc 1 R, f x ∂μ) ≤ 2*C*(R^2+B*R) := by
  let M := ⌊R⌋₊
  let K := Nat.log 2 M
  let T (k : ℕ) : ℝ := 2^k
  let S := τ ⁻¹' Icc 1 R
  let A (k : ℕ) := τ ⁻¹' Icc (T k) (2*T k)
  let u := Finset.range (K+1)
  have hM : 1 ≤ M := (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).mpr (by exact_mod_cast hR)
  have hTK : T K ≤ R := by
    have h := Nat.pow_log_le_self 2 (show M ≠ 0 by omega)
    have hm : T K ≤ (M : ℝ) := by dsimp only [T,K]; exact_mod_cast h
    exact hm.trans (Nat.floor_le (zero_le_one.trans hR))
  have hcover (x : α) (hx : x ∈ S) : ∃ k ∈ u, x ∈ A k := by
    let m := ⌊τ x⌋₊
    let k := Nat.log 2 m
    have hm : 1 ≤ m := (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).mpr
      (by exact_mod_cast hx.1)
    have hk : k ≤ K := Nat.log_mono_right (Nat.floor_le_floor hx.2)
    refine ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_le hk),?_,?_⟩
    · have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
      have hp : T k ≤ (m : ℝ) := by dsimp only [T,k]; exact_mod_cast h
      exact hp.trans (Nat.floor_le (zero_le_one.trans hx.1))
    · have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) m
      have he : (m : ℝ)+1 ≤ (2:ℝ)^(k+1) := by
        exact_mod_cast (Nat.succ_le_of_lt h)
      rw [pow_succ,mul_comm ((2:ℝ)^k)] at he
      exact (Nat.lt_floor_add_one (τ x)).le.trans he
  have hI : IntegrableOn f S μ := by
    apply (integrableOn_finset_iUnion.mpr (fun k (_ : k ∈ u) => (hWin k).1)).mono_set
    intro x hx
    obtain ⟨k,hku,hxk⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hku,hxk⟩⟩
  have hAm (k : ℕ) : MeasurableSet (A k) := measurableSet_Icc.preimage hτ
  have hSm : MeasurableSet S := measurableSet_Icc.preimage hτ
  have hAind (k : ℕ) : Integrable ((A k).indicator f) μ := ((hWin k).1).integrable_indicator (hAm k)
  have hpoint (x : α) : S.indicator f x ≤ ∑ k ∈ u, (A k).indicator f x := by
    have hnn (k : ℕ) : 0 ≤ (A k).indicator f x := by
      by_cases hk : x ∈ A k
      · simpa only [indicator_of_mem hk] using hf x
      · simp only [indicator_of_notMem hk,le_refl]
    by_cases hx : x ∈ S
    · obtain ⟨k,hk,hxk⟩ := hcover x hx
      simpa only [indicator_of_mem hx,indicator_of_mem hxk] using
        Finset.single_le_sum (f := fun j => (A j).indicator f x) (fun j _ => hnn j) hk
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg fun k _ => hnn k
  have hT₂ (k : ℕ) : (T k)^2 = (4 : ℝ)^k := by
    dsimp only [T]
    rw [sq,← mul_pow]
    norm_num
  have hSumOne : (∑ k ∈ u, T k) ≤ 2*R :=
    (spectral_sum_geometric_le_two_last (by norm_num : (2:ℝ)≤2) K).trans
      (mul_le_mul_of_nonneg_left hTK (by norm_num))
  have hSumTwo : (∑ k ∈ u, (T k)^2) ≤ 2*R^2 := by
    simp only [hT₂]
    refine (spectral_sum_geometric_le_two_last (by norm_num : (2:ℝ)≤4) K).trans ?_
    rw [← hT₂]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by dsimp only [T]; positivity) hTK 2)
      (by norm_num)
  refine ⟨hI,?_⟩
  change (∫ x in S, f x ∂μ) ≤ _
  calc
    _ = ∫ x, S.indicator f x ∂μ := (integral_indicator hSm).symm
    _ ≤ ∫ x, ∑ k ∈ u, (A k).indicator f x ∂μ :=
      integral_mono (hI.integrable_indicator hSm) (integrable_finsetSum u (fun k _ => hAind k)) hpoint
    _ = ∑ k ∈ u, ∫ x in A k, f x ∂μ := by
      rw [integral_finsetSum u (fun k _ => hAind k)]
      exact Finset.sum_congr rfl fun k _ => integral_indicator (hAm k)
    _ ≤ ∑ k ∈ u, C*((T k)^2+B*T k) := Finset.sum_le_sum fun k _ => (hWin k).2
    _ = C*((∑ k ∈ u, (T k)^2)+B*(∑ k ∈ u, T k)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ C*(2*R^2+B*(2*R)) := mul_le_mul_of_nonneg_left
      (add_le_add hSumTwo (mul_le_mul_of_nonneg_left hSumOne hB)) hC
    _ = _ := by ring

end ArtinMatthews
