module

public import ArtinMatthews.MarkedBirthRankCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine initial active-tuple cost and the constant ghost rows fit
inside a fixed polynomial per operation at the actual M and N. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedBirth_initial_slots_le_twice_moment {x : ℝ} (hlog : 1 ≤ Real.log x) :
    markedPadSlots x ≤ 2*markedMemoryMomentLength x := by
  have hL : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hM := Nat.floor_le (Real.rpow_nonneg hL (1/100:ℝ))
  have hpow : (Real.log x)^(1/100:ℝ) ≤ (Real.log x)^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hOne : 1 ≤ (Real.log x)^(1/2:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hN := markedMemoryMomentLength_lower hL
  have hh : (markedPadSlots x:ℝ) ≤ 2*(markedMemoryMomentLength x:ℝ) := by
    unfold markedPadSlots
    push_cast
    linarith
  exact_mod_cast hh

theorem markedBirth_high_rank_prefactor_budget (K : ℕ) (C P : ℝ)
    (hC : 1 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ x : ℝ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ (Real.log x)^P →
      (2:ℝ)^(K*markedPadSlots x)*C^(markedMemoryMomentLength x+1)*R^(markedMemoryMomentLength x) ≤
        ((Real.log x)^(P+2))^(markedMemoryMomentLength x+1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max C ((2:ℝ)^(2*K))))] with x hx
  intro R hR hRp
  let L := Real.log x
  let N := markedMemoryMomentLength x
  have hLC : C ≤ L := (le_max_left _ _).trans hx
  have hLbase : (2:ℝ)^(2*K) ≤ L := (le_max_right _ _).trans hx
  have hL₁ : 1 ≤ L := hC.trans hLC
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hinit : (2:ℝ)^(K*markedPadSlots x) ≤ L^(N+1) := by
    calc
      _ ≤ (2:ℝ)^(K*(2*N)) := pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_left K (markedBirth_initial_slots_le_twice_moment hL₁))
      _ = ((2:ℝ)^(2*K))^N := by rw [← pow_mul]; congr 1; ring
      _ ≤ L^N := pow_le_pow_left₀ (by positivity) hLbase N
      _ ≤ L^(N+1) := pow_le_pow_right₀ hL₁ (by omega)
  have hghost : C^(N+1) ≤ L^(N+1) := pow_le_pow_left₀ (zero_le_one.trans hC) hLC _
  have hedge : R^N ≤ (L^P)^(N+1) :=
    (pow_le_pow_left₀ hR hRp N).trans (pow_le_pow_right₀ (Real.one_le_rpow hL₁ hP) (by omega))
  calc
    _ ≤ L^(N+1)*L^(N+1)*(L^P)^(N+1) := by
      exact mul_le_mul (mul_le_mul hinit hghost (pow_nonneg (zero_le_one.trans hC) _) (by positivity))
        hedge (pow_nonneg hR _) (by positivity)
    _ = (L*L*L^P)^(N+1) := by rw [mul_pow,mul_pow]
    _ = _ := by
      congr 1
      calc
        L*L*L^P = (L^(1:ℝ)*L^(1:ℝ))*L^P := by rw [Real.rpow_one]
        _ = L^((1:ℝ)+1+P) := by rw [← Real.rpow_add hL,← Real.rpow_add hL]
        _ = _ := by congr 1; ring

end ArtinMatthews
