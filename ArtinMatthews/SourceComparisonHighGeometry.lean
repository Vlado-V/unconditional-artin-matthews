module

public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit scale inequalities for the original comparison-cell geometry. -/

namespace ArtinMatthews

open Filter
open scoped Topology

noncomputable section

private theorem power_le_exp_power_eventually (A B δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, B*X^A ≤ Real.exp (c*X^δ) := by
  have h : Tendsto (fun X : ℝ => B*(X^A*Real.exp (-c*X^δ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (rpow_mul_exp_neg_rpow_tendsto A hδ hc).const_mul B
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with X hX
  have hx : B*(X^A*Real.exp (-c*X^δ)) ≤ 1 := hX.le
  rw [← mul_assoc, neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hx
  exact (div_le_one (Real.exp_pos _)).mp hx

private theorem rpow_gap_eventually (u v C d : ℝ) (huv : u < v) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, C*X^u ≤ d*X^v := by
  have h : Tendsto (fun X : ℝ => C*X^(u-v)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr huv)).const_mul C
  filter_upwards [h.eventually (gt_mem_nhds hd), eventually_gt_atTop (0:ℝ)] with X hX hX0
  have hh : C*X^(u-v) ≤ d := hX.le
  rw [Real.rpow_sub hX0, ← mul_div_assoc] at hh
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hX0 _)).mp hh

private theorem small_prime_to_window (a : ℝ) (ha : 0 < a) :
    ∀ᶠ X : ℝ in atTop, (16/a)*X*Real.exp (X^(36/100:ℝ)) ≤ Real.exp (X^(38/100:ℝ)) := by
  filter_upwards [power_le_exp_power_eventually 1 (16/a) (38/100) (1/2) (by norm_num) (by norm_num),
    rpow_gap_eventually (36/100) (38/100) 1 (1/2) (by norm_num) (by norm_num)] with X h₁ h₂
  simp only [Real.rpow_one, one_mul] at h₁ h₂
  calc
    _ ≤ Real.exp ((1/2)*X^(38/100:ℝ))*Real.exp ((1/2)*X^(38/100:ℝ)) :=
      mul_le_mul h₁ (Real.exp_le_exp.mpr h₂) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem small_prime_to_residual (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, (8/a)*Real.exp (X^(36/100:ℝ)) ≤ Real.exp ((ε/4)*X) := by
  filter_upwards [power_le_exp_power_eventually 0 (8/a) 1 (ε/8) (by norm_num) (by positivity),
    rpow_gap_eventually (36/100) 1 1 (ε/8) (by norm_num) (by positivity)] with X h₁ h₂
  simp only [Real.rpow_zero, mul_one, Real.rpow_one, one_mul] at h₁ h₂
  calc
    _ ≤ Real.exp ((ε/8)*X)*Real.exp ((ε/8)*X) :=
      mul_le_mul h₁ (Real.exp_le_exp.mpr h₂) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem sourceComparisonHighGeometry_window (a b ε C : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (Y H P L U : ℝ), Real.exp X ≤ Y → Y ≤ Real.exp ((1+ε/4)*X) →
        Real.exp (X^(38/100:ℝ)) ≤ H → H ≤ Real.exp (X/2) →
        1 ≤ P → P ≤ Real.exp (X^(36/100:ℝ)) →
        1 ≤ L → L ≤ Real.exp ((1-ε/2)*X) → 1 ≤ U →
        a*Y ≤ 8*(P*L*U) → P*L*U ≤ b*Y →
        let T := X*Y/H
        X^(max 1 C+1) ≤ T ∧ 1 < 2*T ∧ 2*T ≤ Real.exp (2*X) ∧
          2*T ≤ L*U ∧ P*L*U ≤ Real.exp (3*X) ∧ Real.exp ((ε/4)*X) ≤ U := by
  filter_upwards [eventually_ge_atTop (1:ℝ), small_prime_to_window a ha,
    small_prime_to_residual a ε ha hε,
    power_le_exp_power_eventually (max 1 C+1) 1 1 (1/2) (by norm_num) (by norm_num),
    power_le_exp_power_eventually 1 2 1 (1/2) (by norm_num) (by norm_num),
    power_le_exp_power_eventually 0 b 1 1 (by norm_num) (by norm_num)]
    with X hX hshort hres hshift hlong hb
  intro Y H P L U hY hYcap hH hHcap hP hPcap hL hLcap hU hl hu
  dsimp only
  let T := X*Y/H
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hH1 : 1 ≤ H := (Real.one_le_exp (by positivity)).trans hH
  have hH0 : 0 < H := by linarith
  have hP0 : 0 < P := by linarith
  have hL0 : 0 < L := by linarith
  simp only [one_mul, Real.rpow_one] at hshift hlong
  simp only [Real.rpow_zero, mul_one, Real.rpow_one, one_mul] at hb
  have hTlow : Real.exp (X/2) ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hH0).mpr
    calc
      _ ≤ Real.exp (X/2)*Real.exp (X/2) := by gcongr
      _ = Real.exp X := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Y := hY
      _ ≤ X*Y := by nlinarith
  have hTlong : 2*T ≤ Real.exp (2*X) := by
    have he : 2*T = (2*X*Y)/H := by dsimp [T]; ring
    rw [he]
    calc
      _ ≤ 2*X*Y := div_le_self (by positivity) hH1
      _ ≤ Real.exp ((1/2)*X)*Real.exp ((1+ε/4)*X) :=
        mul_le_mul hlong hYcap hY0.le (Real.exp_pos _).le
      _ ≤ Real.exp (2*X) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
  have hTmid : 2*T ≤ L*U := by
    have hstep : (16/a)*X*P ≤ H :=
      (mul_le_mul_of_nonneg_left hPcap (by positivity)).trans (hshort.trans hH)
    have hh : 2*X*Y ≤ L*U*H := by
      calc
        _ = (2*X/a)*(a*Y) := by field_simp
        _ ≤ (2*X/a)*(8*(P*L*U)) := mul_le_mul_of_nonneg_left hl (by positivity)
        _ = (L*U)*((16/a)*X*P) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)
    have he : 2*T = (2*X*Y)/H := by dsimp [T]; ring
    exact he.trans_le ((div_le_iff₀ hH0).mpr hh)
  have hprod : P*L*U ≤ Real.exp (3*X) := by
    calc
      _ ≤ b*Y := hu
      _ ≤ Real.exp X*Real.exp ((1+ε/4)*X) := by
        exact mul_le_mul hb hYcap hY0.le (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hUlow : Real.exp ((ε/4)*X) ≤ U := by
    have h₁ : (8/a)*P ≤ Real.exp ((ε/4)*X) :=
      (mul_le_mul_of_nonneg_left hPcap (by positivity)).trans hres
    have hh : Real.exp ((ε/4)*X)*(8/a)*P*L ≤ Y := by
      calc
        _ = Real.exp ((ε/4)*X)*((8/a)*P)*L := by ring
        _ ≤ Real.exp ((ε/4)*X)*Real.exp ((ε/4)*X)*Real.exp ((1-ε/2)*X) := by gcongr
        _ = Real.exp X := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := hY
    have hh₁ : Real.exp ((ε/4)*X)*(8*P*L) ≤ a*Y := by
      calc
        _ = a*(Real.exp ((ε/4)*X)*(8/a)*P*L) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hh ha.le
    have hh₂ : a*Y ≤ U*(8*P*L) := hl.trans_eq (by ring)
    exact le_of_mul_le_mul_right (hh₁.trans hh₂) (by positivity)
  have hs : X^(max 1 C+1) ≤ Real.exp (X/2) := by
    simpa only [show (1:ℝ)/2*X=X/2 by ring] using hshift
  exact ⟨hs.trans hTlow,
    by linarith [(Real.one_le_exp (by positivity : 0 ≤ X/2)).trans hTlow],
    hTlong, hTmid, hprod, hUlow⟩

theorem sourceComparisonHighGeometry_divisor (ε D : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ (U d : ℝ), Real.exp ((ε/4)*X) ≤ U →
      0 < d → d ≤ Real.exp (D*X^(47/100:ℝ)) → Real.exp ((ε/8)*X) ≤ U/d := by
  filter_upwards [rpow_gap_eventually (47/100) 1 D (ε/8) (by norm_num) (by positivity)] with X hX
  simp only [Real.rpow_one] at hX
  intro U d hU hd hdc
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ Real.exp ((ε/8)*X)*Real.exp ((ε/8)*X) :=
      mul_le_mul_of_nonneg_left (hdc.trans (Real.exp_le_exp.mpr hX)) (Real.exp_pos _).le
    _ = Real.exp ((ε/4)*X) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := hU

end
end ArtinMatthews
