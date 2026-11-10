module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The exact frozen-prime weight and geometric Dirichlet series
in the Section 04 reflected expansion. -/
namespace ArtinMatthews.SourceEulerAssembly
open scoped Classical BigOperators
noncomputable section

def sourceReflectionFrozenLocalWeight (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then q ^ (1 / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

def sourceReflectionFrozenLocalTerm (q σ : ℝ) (e : ℕ) : ℝ :=
  sourceReflectionFrozenLocalWeight q e * q ^ (-σ * (e : ℝ))

def sourceReflectionFrozenLocalFactor (q σ : ℝ) : ℝ :=
  1 + (q ^ (-σ) + q ^ (-1 / 2 - 3 * σ)) / (1 - q ^ (-1 - 3 * σ))

theorem sourceReflectionFrozenLocalTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (σ : ℝ) (e : ℕ) :
    0 ≤ sourceReflectionFrozenLocalTerm q σ e := by
  unfold sourceReflectionFrozenLocalTerm sourceReflectionFrozenLocalWeight
  apply mul_nonneg _ (Real.rpow_nonneg hq _)
  split_ifs <;> positivity

@[simp] theorem sourceReflectionFrozenLocalTerm_zero (q σ : ℝ) :
    sourceReflectionFrozenLocalTerm q σ 0 = 1 := by
  simp [sourceReflectionFrozenLocalTerm, sourceReflectionFrozenLocalWeight]

theorem sourceReflectionFrozenLocalTerm_one {q : ℝ} (hq : 0 < q) (σ : ℝ) (k : ℕ) :
    sourceReflectionFrozenLocalTerm q σ (3 * k + 1) =
      q ^ (-σ) * (q ^ (-1 - 3 * σ)) ^ k := by
  have hn : 3 * k + 1 ≠ 0 := by omega
  have hr : (3 * k + 1) % 3 = 1 := by omega
  have hd : (3 * k + 1) / 3 = k := by omega
  rw [sourceReflectionFrozenLocalTerm, sourceReflectionFrozenLocalWeight, ite_eq_right hn,
    ite_eq_left hr, hd, ← Real.rpow_natCast (q ^ (-1 - 3 * σ)) k, ← Real.rpow_mul hq.le,
    ← Real.rpow_add hq, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem sourceReflectionFrozenLocalTerm_three {q : ℝ} (hq : 0 < q) (σ : ℝ) (k : ℕ) :
    sourceReflectionFrozenLocalTerm q σ (3 * (k + 1)) =
      q ^ (-1 / 2 - 3 * σ) * (q ^ (-1 - 3 * σ)) ^ k := by
  have hn : 3 * (k + 1) ≠ 0 := by omega
  have hr : (3 * (k + 1)) % 3 = 0 := by omega
  have hd : (3 * (k + 1)) / 3 = k + 1 := by omega
  have hr' : (3 * (k + 1)) % 3 ≠ 1 := hr.trans_ne Nat.zero_ne_one
  rw [sourceReflectionFrozenLocalTerm, sourceReflectionFrozenLocalWeight, ite_eq_right hn,
    ite_eq_right hr', ite_eq_left hr, hd, ← Real.rpow_natCast (q ^ (-1 - 3 * σ)) k,
    ← Real.rpow_mul hq.le, ← Real.rpow_add hq, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem sourceReflectionFrozenLocalTerm_two (q σ : ℝ) (k : ℕ) :
    sourceReflectionFrozenLocalTerm q σ (3 * k + 2) = 0 := by
  have hr : (3 * k + 2) % 3 = 2 := by omega
  simp [sourceReflectionFrozenLocalTerm, sourceReflectionFrozenLocalWeight, hr]

theorem sourceReflectionFrozenLocalRatio_le {q σ : ℝ} (hq : 2 ≤ q) (hσ : 0 ≤ σ) :
    q ^ (-1 - 3 * σ) ≤ 1 / 2 := by
  calc
    _ ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    _ = _ := by norm_num

theorem sourceReflectionFrozenLocal_hasSum {q σ : ℝ} (hq : 2 ≤ q) (hσ : 0 ≤ σ) :
    HasSum (sourceReflectionFrozenLocalTerm q σ) (sourceReflectionFrozenLocalFactor q σ) := by
  let r := q ^ (-1 - 3 * σ)
  have hq₀ : 0 < q := by linarith
  have hr₀ : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := (sourceReflectionFrozenLocalRatio_le hq hσ).trans_lt (by norm_num)
  have hgeo := summable_geometric_of_lt_one hr₀ hr₁
  let s (j : Fin 3) (k : ℕ) := sourceReflectionFrozenLocalTerm q σ (3 * k + j.val)
  have hzero (k : ℕ) :
      s 0 (k + 1) = q ^ (-1 / 2 - 3 * σ) * r ^ k := by
    simpa only [s, Fin.val_zero, add_zero, r] using sourceReflectionFrozenLocalTerm_three hq₀ σ k
  have hone (k : ℕ) : s 1 k = q ^ (-σ) * r ^ k :=
    sourceReflectionFrozenLocalTerm_one hq₀ σ k
  have htwo (k : ℕ) : s 2 k = 0 := sourceReflectionFrozenLocalTerm_two q σ k
  have hs₀ : Summable (s 0) :=
    (summable_nat_add_iff 1).mp ((hgeo.mul_left _).congr (fun k => (hzero k).symm))
  have hs₁ : Summable (s 1) := (hgeo.mul_left _).congr (fun k => (hone k).symm)
  have hs₂ : Summable (s 2) := summable_zero.congr (fun k => (htwo k).symm)
  have hs (j : Fin 3) : Summable (s j) := by
    fin_cases j
    · exact hs₀
    · exact hs₁
    · exact hs₂
  let e : (Fin 3 × ℕ) ≃ ℕ := (Equiv.prodComm _ _).trans (Nat.divModEquiv 3).symm
  have he (a : Fin 3 × ℕ) : e a = 3 * a.2 + a.1.val := by
    change a.2 * 3 + a.1.val = _
    omega
  have hsum : Summable (fun a : Fin 3 × ℕ => s a.1 a.2) :=
    (summable_prod_of_nonneg (fun a => sourceReflectionFrozenLocalTerm_nonneg hq₀.le σ _)).2
      ⟨hs, (hasSum_fintype _).summable⟩
  have hf : Summable (sourceReflectionFrozenLocalTerm q σ) :=
    e.summable_iff.mp (hsum.congr (fun a => congrArg (sourceReflectionFrozenLocalTerm q σ) (he a).symm))
  apply hf.hasSum_iff.mpr
  calc
    _ = ∑' a : Fin 3 × ℕ, s a.1 a.2 := by
      rw [← e.tsum_eq (sourceReflectionFrozenLocalTerm q σ)]
      exact tsum_congr (fun a => congrArg (sourceReflectionFrozenLocalTerm q σ) (he a))
    _ = ∑ j : Fin 3, ∑' k, s j k := by
      rw [hsum.tsum_prod' hs, tsum_fintype]
    _ = _ := by
      rw [Fin.sum_univ_three, hs₀.tsum_eq_zero_add, tsum_congr hzero, tsum_congr hone,
        tsum_congr htwo, tsum_zero, tsum_mul_left, tsum_mul_left,
        tsum_geometric_of_lt_one hr₀ hr₁]
      simp only [s, mul_zero, Fin.val_zero, add_zero, sourceReflectionFrozenLocalTerm_zero]
      unfold sourceReflectionFrozenLocalFactor
      rw [div_eq_mul_inv]
      ring

theorem sourceReflectionFrozenLocalFactor_nonneg {q σ : ℝ} (hq : 2 ≤ q) (hσ : 0 ≤ σ) :
    0 ≤ sourceReflectionFrozenLocalFactor q σ := by
  have hq₀ : 0 ≤ q := by linarith
  have hr : 0 ≤ 1 - q ^ (-1 - 3 * σ) := by
    linarith [sourceReflectionFrozenLocalRatio_le hq hσ]
  exact add_nonneg zero_le_one
    (div_nonneg (add_nonneg (Real.rpow_nonneg hq₀ _) (Real.rpow_nonneg hq₀ _)) hr)

theorem sourceReflectionFrozenLocalFactor_le {q σ : ℝ} (hq : 2 ≤ q) (hσ : 0 ≤ σ) :
    sourceReflectionFrozenLocalFactor q σ ≤ 3 + Real.sqrt 2 := by
  have h₁ : q ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h₂ : q ^ (-1 / 2 - 3 * σ) ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num))
  have hr : 1 / 2 ≤ 1 - q ^ (-1 - 3 * σ) := by
    linarith [sourceReflectionFrozenLocalRatio_le hq hσ]
  unfold sourceReflectionFrozenLocalFactor
  have h := div_le_div_of_nonneg_right (add_le_add h₁ h₂) (by linarith : 0 ≤ 1 - q ^ (-1 - 3 * σ))
  have ht : 0 ≤ 1 + (2 : ℝ) ^ (-1 / 2 : ℝ) := by positivity
  have hc : (1 + (2 : ℝ) ^ (-1 / 2 : ℝ)) / (1 / 2) = 2 + Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    have hx : (2 : ℝ) * (2 : ℝ) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (2 : ℝ)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    calc
      _ = 2 + 2 * (2 : ℝ) ^ (-1 / 2 : ℝ) := by ring
      _ = _ := by rw [hx]
  calc
    _ ≤ 1 + (1 + (2 : ℝ) ^ (-1 / 2 : ℝ)) / (1 - q ^ (-1 - 3 * σ)) :=
      add_le_add le_rfl h
    _ ≤ 1 + (1 + (2 : ℝ) ^ (-1 / 2 : ℝ)) / (1 / 2) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left ht (by norm_num) hr)
    _ = _ := by rw [hc]; ring

end
end ArtinMatthews.SourceEulerAssembly
