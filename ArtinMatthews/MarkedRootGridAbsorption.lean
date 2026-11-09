module

public import ArtinMatthews.MarkedRootGridBudget
public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The c/8 grid retains all cell errors and the actual subpower path-height
and enumeration costs. A fixed power then beats the growing moment target. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedRootGrid_height_small (a B c : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,∀ H : ℝ,0 ≤ H → H ≤ Real.exp (B*(Real.log x)^a) →
      20*H/(markedRootGridSize c x : ℝ) ≤ 1/2 := by
  have hlim : Tendsto (fun x : ℝ => 20*x^(-c/16)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_div] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < c/16)).const_mul 20
  filter_upwards [marked_sublinear_log_exp_le_rpow_eventually a B (c/16) ha (by positivity),
    hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2)),eventually_ge_atTop (1:ℝ)]
    with x hg hl hx
  intro H hH hHb
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hn := markedRootGridSize_bounds hc hx
  have hHp : H ≤ x^(c/16) := hHb.trans hg
  have hbound : H/(markedRootGridSize c x : ℝ) ≤ x^(-c/16) := by
    calc
      _ = H*(1/(markedRootGridSize c x : ℝ)) := by ring
      _ ≤ x^(c/16)*x^(-c/8) := mul_le_mul hHp hn.2.2 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤20)
  have hal : 0 ≤ a := ha₀
  simpa only [mul_div_assoc] using hh.trans hl.le

theorem markedRootGrid_actual_budget (a B C c E D A : ℝ)
    (ha₀ : 0 ≤ a) (ha : a < 1) (hB : 0 ≤ B) (hc : 0 < c)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,∀ H : ℝ,0 ≤ H → H ≤ Real.exp (B*(Real.log x)^a) →
      Real.exp (C*(Real.log x)^a)*
        (E*15*(markedRootGridSize c x : ℝ)^3*x^(-c) + D*H/(markedRootGridSize c x : ℝ)) ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x : ℝ)) := by
  let K := 120*E+D
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [marked_sublinear_log_exp_le_rpow_eventually a (B+C+K) (c/16) ha (by positivity),
    markedRoot_power_le_moment_log (c/16) A (by positivity) hA,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (1:ℝ)]
    with x hg hm hL hx
  intro H hH hHb
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ht : 1 ≤ (Real.log x)^a := Real.one_le_rpow hL ha₀
  have hR : 1 ≤ Real.exp (B*(Real.log x)^a) := Real.one_le_exp (mul_nonneg hB (Real.rpow_nonneg (by linarith) _))
  have hdecay : x^(-5*c/8) ≤ x^(-c/8) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hgrid := mul_le_mul_of_nonneg_left (markedRootGridSize_discrepancy hc hx) hE
  have hmesh := (markedRootGridSize_bounds hc hx).2.2
  have hinside : E*15*(markedRootGridSize c x : ℝ)^3*x^(-c)+D*H/(markedRootGridSize c x : ℝ) ≤
      K*Real.exp (B*(Real.log x)^a)*x^(-c/8) := by
    have hfirst : E*15*(markedRootGridSize c x : ℝ)^3*x^(-c) ≤
        (120*E)*Real.exp (B*(Real.log x)^a)*x^(-c/8) := by
      calc
        _ ≤ (120*E)*x^(-5*c/8) := by
          simpa only [mul_assoc,mul_comm,mul_left_comm] using hgrid
        _ ≤ _ := mul_le_mul (le_mul_of_one_le_right (by positivity : 0 ≤ 120*E) hR) hdecay
          (Real.rpow_nonneg hx0.le _) (by positivity)
    have hsecond : D*H/(markedRootGridSize c x : ℝ) ≤ D*Real.exp (B*(Real.log x)^a)*x^(-c/8) := by
      have hh := mul_le_mul hHb hmesh (by positivity : 0 ≤ 1/(markedRootGridSize c x : ℝ))
        (Real.exp_pos _).le
      have hh' := mul_le_mul_of_nonneg_left hh hD
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using hh'
    exact (add_le_add hfirst hsecond).trans_eq (by dsimp only [K]; ring)
  have hconst : K ≤ Real.exp (K*(Real.log x)^a) := by
    apply (show K ≤ Real.exp K by linarith [Real.add_one_le_exp K]).trans
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ Real.exp (C*(Real.log x)^a)*(K*Real.exp (B*(Real.log x)^a)*x^(-c/8)) :=
      mul_le_mul_of_nonneg_left hinside (Real.exp_pos _).le
    _ ≤ Real.exp (C*(Real.log x)^a)*(Real.exp (K*(Real.log x)^a)*Real.exp (B*(Real.log x)^a)*x^(-c/8)) := by
      gcongr
    _ = Real.exp ((B+C+K)*(Real.log x)^a)*x^(-c/8) := by
      rw [← mul_assoc,← mul_assoc,← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    _ ≤ x^(c/16)*x^(-c/8) := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx0.le _)
    _ = x^(-c/16) := by rw [← Real.rpow_add hx0]; congr 1; ring
    _ ≤ _ := by simpa only [neg_div] using hm

end ArtinMatthews
