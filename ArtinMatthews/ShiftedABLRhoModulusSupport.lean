module

public import ArtinMatthews.ShiftedABLRhoSignedSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! The common logarithmic test has a wider finite modulus support
than the original circle weight. The extra moduli have zero original weight. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

def shiftedABLCommonModuli (r L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (18*L)).filter (fun c => c.Coprime r)

theorem shiftedABLMellinModuli_subset_common {F r L : ℕ} (hF : 0 < F) (hL : 0 < L) :
    shiftedABLMellinModuli F r L ⊆ shiftedABLCommonModuli r L := by
  intro c hc
  obtain ⟨hlo,hhi,hcop⟩ := shiftedABLMellinModuli_bounds hF hc
  have hF₁ : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hL₀ : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hc₀ : 0 < (c : ℝ) := (by positivity : 0 < 3*(L : ℝ)/(F : ℝ)).trans_le hlo
  have hc₁ : 1 ≤ c := Nat.cast_pos.mp hc₀
  have hUpper : (c : ℝ) ≤ 18*(L : ℝ) := by
    calc
      _ ≤ 2*(3*(L : ℝ)/(F : ℝ)) := hhi
      _ ≤ 2*(3*(L : ℝ)) := mul_le_mul_of_nonneg_left (div_le_self (by positivity) hF₁) (by norm_num)
      _ ≤ _ := by linarith
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hc₁,by exact_mod_cast hUpper⟩,hcop⟩

theorem shiftedABLMellinModulusWeight_zero_off_circle {F r L c : ℕ}
    (hF : 0 < F) (hL : 0 < L) (hcop : r.Coprime F) (hc : c.Coprime r)
    (hout : c ∉ shiftedABLMellinModuli F r L) (z : ℝ × ℝ) :
    shiftedABLMellinModulusWeight F L z (c : ℝ) = 0 := by
  by_contra h
  obtain ⟨hlo,hhi⟩ := shiftedABLMellinModulusWeight_support hF hL z h
  have hF₀ : (0 : ℝ) < F := Nat.cast_pos.mpr hF
  have hL' : 3*L ≤ F*c := by
    have he := (div_le_iff₀ hF₀).mp hlo
    rw [mul_comm (c : ℝ)] at he
    exact_mod_cast he
  have hU' : F*c ≤ 6*L := by
    have he := (le_div_iff₀ hF₀).mp (show (c : ℝ) ≤ (6*(L : ℝ))/(F : ℝ) from
      hhi.trans_eq (by ring))
    rw [mul_comm (c : ℝ)] at he
    exact_mod_cast he
  apply hout
  refine Finset.mem_image.mpr ⟨F*c,?_,?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hL',hU'⟩,dvd_mul_right F c,
      Nat.coprime_mul_iff_left.mpr ⟨hcop.symm,hc⟩⟩
  · exact Nat.mul_div_cancel_left c hF

theorem shiftedABLRhoCommonTest_zero_of_modulus_large {F L n r c : ℕ} {R : ℝ} {ρ : ℤ}
    (hF : 0 < F) (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hR : 0 < R) (hρ : (ρ.natAbs : ℝ) ≤ 2*R) (hc : 18*L < c) (u : ℝ) :
    shiftedABLRhoCommonTest (shiftedABLRhoBlockScale L n r R) u
      (shiftedABLRhoOrbitalArgument F n r ρ c) = 0 := by
  let a := shiftedABLRhoBlockScale L n r R
  let x := shiftedABLRhoOrbitalArgument F n r ρ c
  let Q : ℝ := 3*(L : ℝ)
  have ha : 0 < a := shiftedABLRhoBlockScale_pos hL hn hr hR
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hr₀ : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
  have hcCast : (18 : ℝ)*(L : ℝ) < c := by exact_mod_cast hc
  have hc₀ : (6 : ℝ)*Q < c := by dsimp only [Q]; linarith only [hcCast]
  have hc₁ : 0 < (c : ℝ) := (by positivity : 0 < 6*Q).trans hc₀
  have hF₁ : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hFc : (6 : ℝ)*Q < (F : ℝ)*c :=
    hc₀.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hF₁ hc₁.le)
  have hS : Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) ≤ 2*Real.sqrt (R*(n : ℝ)) := by
    have hm : (ρ.natAbs : ℝ)*(n : ℝ) ≤ 4*(R*(n : ℝ)) := by
      calc
        _ ≤ (2*R)*(n : ℝ) := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg n)
        _ ≤ _ := by nlinarith only [mul_nonneg hR.le (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    have he := Real.sqrt_le_sqrt hm
    rwa [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)),show Real.sqrt (4 : ℝ) = 2 by norm_num] at he
  have hx : x ≤ 2*a*Q/((F : ℝ)*c) := by
    unfold x shiftedABLRhoOrbitalArgument shiftedABLMellinJNumerator
    calc
      _ ≤ (4*Real.pi*(2*Real.sqrt (R*(n : ℝ))))/((F : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) (by positivity)
      _ = _ := by
        dsimp only [a,Q,shiftedABLRhoBlockScale]
        field_simp [hr₀.ne',hQ.ne']
  have hxa : x < a/3 := by
    apply hx.trans_lt
    apply (div_lt_iff₀ (by positivity : 0 < (F : ℝ)*c)).mpr
    have hh := mul_lt_mul_of_pos_left hFc (show 0 < a/3 by positivity)
    linarith
  by_contra h
  exact hxa.not_ge ((shiftedABLRhoCommonTest_tsupport a u ha) (subset_tsupport _ h)).1

end ArtinMatthews
