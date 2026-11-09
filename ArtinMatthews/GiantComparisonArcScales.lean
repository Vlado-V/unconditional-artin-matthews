module

public import ArtinMatthews.GiantComparisonScale


set_option backward.privateInPublic true
@[expose] public section

/-! The scales of an occupied pair of logarithmic cells fit the
centered-endpoint and major-arc frequency windows. -/
namespace ArtinMatthews

open Filter
noncomputable section

theorem giantComparisonArcScales_eventually (c d C a ε : ℝ)
    (hc : (19/50 : ℝ) ≤ c) (hd : d < 1) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ U V : ℕ,
      Real.exp ((Real.log x)^c)/4 ≤ (U : ℝ) →
      Real.exp ((Real.log x)^c)/4 ≤ (V : ℝ) →
      (U : ℝ) ≤ Real.exp (C*Real.log (Real.log x)*(Real.log x)^d) →
      (V : ℝ) ≤ Real.exp (C*Real.log (Real.log x)*(Real.log x)^d) →
      let L := Real.log x
      let Q := L^a
      let Y := x*((U : ℝ)*(V : ℝ))
      let H := ((U : ℝ)*(V : ℝ))/Q
      x ≤ Y ∧ Y ≤ x^(1+ε/4) ∧ 1 ≤ Q ∧
        Real.exp (L^(19/50 : ℝ)) ≤ H ∧ H ≤ Real.exp (L/2) ∧
        1 ≤ H ∧ H ≤ Y ∧ L*(Y/H) = x*L^(a+1) := by
  filter_upwards [giantComparisonScale_eventually c d C a (ε/4)
    ((by norm_num : (0 : ℝ) < 19/50).trans_le hc) hd hC ha (by positivity),
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hscale hx hL
  intro U V hU hV hUp hVp
  let L := Real.log x
  let W := (U : ℝ)*(V : ℝ)
  let Q := L^a
  let Y := x*W
  let H := W/Q
  obtain ⟨hYlo,hYhi,hQ,hHlo,hHone,hHY,hheight⟩ := hscale U V hU hV hUp hVp
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hW : W ≤ x^(ε/4) := by
    apply le_of_mul_le_mul_left _ hx₀
    calc
      x * W ≤ x^(1+ε/4) := hYhi
      _ = x*x^(ε/4) := by rw [Real.rpow_add hx₀, Real.rpow_one]
  have hHup : H ≤ Real.exp (L/2) := by
    have hQ' : 1 ≤ Q := hQ
    calc
      H ≤ W := div_le_self (by positivity) hQ'
      _ ≤ x^(ε/4) := hW
      _ ≤ x^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = Real.exp (L/2) := by rw [Real.rpow_def_of_pos hx₀]; congr 1; dsimp [L]; ring
  exact ⟨hYlo,hYhi,hQ,
    (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hc)).trans hHlo,
    hHup,hHone,hHY,hheight⟩

theorem giantComparisonMellinPhase_time_le {L v : ℝ} (hL : 2*Real.pi ≤ L)
    (hv : |v| ≤ L) : |-2*Real.pi*v| ≤ L^(2 : ℝ) := by
  rw [abs_mul, show |(-2 : ℝ)*Real.pi| = 2*Real.pi by
    rw [abs_mul, abs_of_pos Real.pi_pos]; norm_num, Real.rpow_two]
  simpa only [pow_two] using
    mul_le_mul hL hv (abs_nonneg _) ((by positivity : 0 ≤ 2*Real.pi).trans hL)

end
end ArtinMatthews
