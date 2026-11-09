module

public import ArtinMatthews.ShiftedABLLevelPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Rescaling the first-variable interval by a fixed bad-level divisor
preserves the original shifted-bilinear budget, including intervals whose
rescaled lower endpoint is below one. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABLLevel_main_bound {x lo hi : ℝ} {d N : ℕ}
    (hx : 0 ≤ x) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hd : 0 < d) (hdN : d ≤ N) :
    x*(max 1 (lo/(d : ℝ)))^(-(1/2) : ℝ) +
      x^(7/8 : ℝ)*(hi/(d : ℝ))^(3/8 : ℝ) ≤
      (N : ℝ)*(x*lo^(-(1/2) : ℝ)+x^(7/8 : ℝ)*hi^(3/8 : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1 : ℝ) ≤ N := hd1.trans (Nat.cast_le.mpr hdN)
  have hlo0 : 0 < lo := zero_lt_one.trans_le hlo
  have hhi0 : 0 ≤ hi := (zero_le_one.trans hlo).trans hhi
  have hsqrt : Real.sqrt (d : ℝ) ≤ N :=
    (Real.sqrt_le_iff.2 ⟨hd0.le,by nlinarith⟩).trans (Nat.cast_le.mpr hdN)
  have hfirst : (max 1 (lo/(d : ℝ)))^(-(1/2) : ℝ) ≤
      (N : ℝ)*lo^(-(1/2) : ℝ) := by
    calc
      _ ≤ (lo/(d : ℝ))^(-(1/2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hlo0 hd0) (le_max_right _ _) (by norm_num)
      _ = Real.sqrt (d : ℝ)*lo^(-(1/2) : ℝ) := by
        rw [Real.div_rpow hlo0.le hd0.le,Real.rpow_neg hd0.le,div_inv_eq_mul,
          ← Real.sqrt_eq_rpow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hlo0.le _)
  have hsecond : (hi/(d : ℝ))^(3/8 : ℝ) ≤ (N : ℝ)*hi^(3/8 : ℝ) := by
    calc
      _ ≤ hi^(3/8 : ℝ) := Real.rpow_le_rpow (div_nonneg hhi0 hd0.le)
        ((div_le_iff₀ hd0).mpr (by nlinarith)) (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hhi0 _) hN1
  calc
    _ ≤ x*((N : ℝ)*lo^(-(1/2) : ℝ))+
        x^(7/8 : ℝ)*((N : ℝ)*hi^(3/8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hx)
        (mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg hx _))
    _ = _ := by ring

theorem shiftedABLLevelRow_interval {N d m : ℕ} {A : Finset ℕ} {lo hi : ℝ}
    (hN : N ≠ 0) (hlo : 1 ≤ lo)
    (hA : ∀ a ∈ A, Squarefree a ∧ lo ≤ (a : ℝ) ∧ (a : ℝ) ≤ hi)
    (hd : 0 < d) (hm : m ∈ shiftedABLLevelRow N A d) :
    Squarefree m ∧ m.Coprime N ∧ max 1 (lo/(d : ℝ)) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ hi/(d : ℝ) := by
  have hAsource : ∀ a ∈ A, 0 < a ∧ Squarefree a := by
    intro a ha
    exact ⟨by exact_mod_cast zero_lt_one.trans_le (hlo.trans (hA a ha).2.1),(hA a ha).1⟩
  obtain ⟨hmp,hmsq,hmN⟩ := shiftedABLLevelRow_source hN hAsource hm
  have hbounds := (hA _ (shiftedABLLevelRow_mem hm).1).2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmp
  have hlo' : lo/(d : ℝ) ≤ m := (div_le_iff₀ hd0).mpr (by
    simpa only [Nat.cast_mul,mul_comm] using hbounds.1)
  have hhi' : (m : ℝ) ≤ hi/(d : ℝ) := (le_div_iff₀ hd0).mpr (by
    simpa only [Nat.cast_mul,mul_comm] using hbounds.2)
  exact ⟨hmsq,hmN,max_le hm1 hlo',hhi'⟩

end ArtinMatthews
