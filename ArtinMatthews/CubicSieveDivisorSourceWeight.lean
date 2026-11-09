module

public import ArtinMatthews.CubicSieveDivisorSmoothProgression
public import Mathlib.Analysis.Calculus.ContDiff.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The source weight is sampled at the predecessor n - 1. -/

noncomputable section
namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators ContDiff

def cubicSieveShiftedDivisorTest (Φ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Φ ((t - 1) / x)

theorem cubicSieve_divisorSourceWeight_reindex (d r : ℕ) (Φ : ℝ → ℝ)
    {x : ℝ} (hx : 1 ≤ x) (hs : Function.support Φ ⊆ Set.Ioo 1 2) :
    (∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) * cubicSieveShiftedDivisorCoefficient d r (u + 1)) =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊3 * x⌋₊, cubicSieveShiftedDivisorTest Φ x n *
        cubicSieveShiftedDivisorCoefficient d r n := by
  let S := Icc 2 (⌊2 * x⌋₊ + 1)
  let T := Ioc ⌊x⌋₊ ⌊3 * x⌋₊
  let F (n : ℕ) := cubicSieveShiftedDivisorTest Φ x n * cubicSieveShiftedDivisorCoefficient d r n
  have hx₀ := zero_lt_one.trans_le hx
  have hmem (n : ℕ) (h : F n ≠ 0) : n ∈ S ∧ n ∈ T := by
    have hf : Φ (((n : ℝ) - 1) / x) ≠ 0 := fun hf =>
      h (by simp only [F, cubicSieveShiftedDivisorTest, hf, zero_mul])
    have hφ := hs hf
    have hlo := (lt_div_iff₀ hx₀).mp hφ.1
    have hhi := (div_lt_iff₀ hx₀).mp hφ.2
    have hn₂ : 2 ≤ n := by
      by_contra! hn
      have h' : (n : ℝ) < 2 := by exact_mod_cast hn
      linarith only [hx, hlo, h']
    have hN : n - 1 ≤ ⌊2 * x⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      exact hhi.le
    refine ⟨mem_Icc.mpr ⟨hn₂, by omega⟩, mem_Ioc.mpr ⟨?_, ?_⟩⟩
    · by_contra! hN
      have h' := (Nat.cast_le.mpr hN).trans (Nat.floor_le hx₀.le)
      linarith only [hlo, h']
    · exact Nat.le_floor (by linarith only [hhi, hx])
  calc
    _ = ∑ n ∈ S, F n := by
      apply sum_bij (fun u _ => u + 1)
      · intro u hu
        obtain ⟨h₁, h₂⟩ := mem_Icc.mp hu
        exact mem_Icc.mpr ⟨by omega, Nat.add_le_add_right h₂ 1⟩
      · intro u _ v _ h
        exact Nat.add_right_cancel h
      · intro n hn
        obtain ⟨h₁, h₂⟩ := mem_Icc.mp hn
        exact ⟨n - 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro u _
        simp only [F, cubicSieveShiftedDivisorTest, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    _ = ∑ n ∈ S ∪ T, F n := sum_subset subset_union_left (by
      intro n _ hn
      by_contra h
      exact hn (hmem n h).1)
    _ = _ := (sum_subset subset_union_right (by
      intro n _ hn
      by_contra h
      exact hn (hmem n h).2)).symm

theorem cubicSieve_shiftedDivisorTest_hasDerivAt (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ)
    (x t : ℝ) :
    HasDerivAt (cubicSieveShiftedDivisorTest Φ x) (deriv Φ ((t - 1) / x) / x) t := by
  have h := (hΦ ((t - 1) / x)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const 1).div_const x)
  unfold cubicSieveShiftedDivisorTest
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h

theorem cubicSieve_divisorSourceWeight_smooth_error {d r : ℕ} (hd : 0 < d)
    (hr : Squarefree r) (hc : d.Coprime r) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x)
    (hlevel : (d : ℝ) ^ 2 * (r : ℝ) ^ 2 ≤ x) :
    |(∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) * cubicSieveShiftedDivisorCoefficient d r (u + 1)) -
      ∫ t in Set.Ioc x (3 * x), cubicSieveShiftedDivisorTest Φ x t *
        cubicSieveShiftedDivisorLogDensity d r t| ≤
      (34 * (2 : ℝ) ^ d.primeFactors.card * (3 : ℝ) ^ r.primeFactors.card *
        Real.sqrt ((3 * x) / (r : ℝ))) *
        ∫ t in Set.Ioc x (3 * x), |deriv (cubicSieveShiftedDivisorTest Φ x) t| := by
  rw [cubicSieve_divisorSourceWeight_reindex d r Φ hx hs]
  have hx₀ := zero_lt_one.trans_le hx
  have hD := hΦ.differentiable (by simp)
  have hφd (t : ℝ) := cubicSieve_shiftedDivisorTest_hasDerivAt Φ hD x t
  have hcont : Continuous (deriv (cubicSieveShiftedDivisorTest Φ x)) := by
    rw [show deriv (cubicSieveShiftedDivisorTest Φ x) = fun t => deriv Φ ((t - 1) / x) / x from
      funext (fun t => (hφd t).deriv)]
    exact ((hΦ.continuous_deriv (by simp)).comp
      ((continuous_id.sub continuous_const).div_const x)).div_const x
  have hleft : cubicSieveShiftedDivisorTest Φ x x = 0 := by
    by_contra h
    have h' := hs h
    have hlo := (lt_div_iff₀ hx₀).mp h'.1
    linarith only [hlo]
  have hright : cubicSieveShiftedDivisorTest Φ x (3 * x) = 0 := by
    by_contra h
    have h' := hs h
    have hhi := (div_lt_iff₀ hx₀).mp h'.2
    linarith only [hx, hhi]
  exact cubicSieve_shiftedDivisorProgression_smooth_error hd hr hc
    (cubicSieveShiftedDivisorTest Φ x) hx₀ (by linarith only [hx]) hlevel
    (fun t _ => (hφd t).differentiableAt) hcont.continuousOn hleft hright

end ArtinMatthews
