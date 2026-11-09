module

public import ArtinMatthews.GiantComparisonCellScale


set_option backward.privateInPublic true
@[expose] public section

/-! The source scales Y=xUV and H=UV/Q give the exact retained
Mellin height and exponential separation from the small-prime band. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantComparisonScale_eventually (c d C a ε : ℝ)
    (hc : 0 < c) (hd : d < 1) (hC : 0 ≤ C) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ U V : ℕ,
      Real.exp ((Real.log x)^c)/4 ≤ (U : ℝ) →
      Real.exp ((Real.log x)^c)/4 ≤ (V : ℝ) →
      (U : ℝ) ≤ Real.exp (C*Real.log (Real.log x)*(Real.log x)^d) →
      (V : ℝ) ≤ Real.exp (C*Real.log (Real.log x)*(Real.log x)^d) →
      let L := Real.log x
      let Q := L^a
      let Y := x*((U : ℝ)*(V : ℝ))
      let H := ((U : ℝ)*(V : ℝ))/Q
      x ≤ Y ∧ Y ≤ x^(1+ε) ∧ 1 ≤ Q ∧ Real.exp (L^c) ≤ H ∧
        1 ≤ H ∧ H ≤ Y ∧ L*(Y/H) = x*L^(a+1) := by
  have hfast := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/16))
  filter_upwards [Real.tendsto_log_atTop.eventually hfast,
    giantComparisonCellScale_subpower (2*C) d ε (by positivity) hd hε,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with
    x hfast hsmall hx hL
  let L := Real.log x
  let Q := L^a
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL ha
  have hQp : 0 < Q := zero_lt_one.trans_le hQ1
  intro U V hU hV hu hv
  dsimp only
  let W := (U : ℝ)*(V : ℝ)
  have hW0 : 0 < W := mul_pos ((by positivity : 0 < Real.exp (L^c)/4).trans_le hU)
    ((by positivity : 0 < Real.exp (L^c)/4).trans_le hV)
  have hW1 : 1 ≤ W := by
    have hU1 : 1 ≤ U := Nat.cast_pos.mp ((by positivity : 0 < Real.exp (L^c)/4).trans_le hU)
    have hV1 : 1 ≤ V := Nat.cast_pos.mp ((by positivity : 0 < Real.exp (L^c)/4).trans_le hV)
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hU1) (by exact_mod_cast hV1)
  have hWupper : W ≤ x^ε := by
    calc
      _ ≤ Real.exp (C*Real.log L*L^d)*Real.exp (C*Real.log L*L^d) :=
        mul_le_mul hu hv (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((2*C)*Real.log L*L^d) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hsmall
  have hHlo : Real.exp (L^c) ≤ W/Q := by
    have hq : Q ≤ Real.exp (L^c)/16 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
      have hb : Q / Real.exp (L^c) ≤ 1/16 := by
        simpa only [Q, L, neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hfast.le
      have hb' := (div_le_iff₀ (Real.exp_pos (L^c))).mp hb
      linarith
    have hw := mul_le_mul hU hV (by positivity : 0 ≤ Real.exp (L^c)/4) (Nat.cast_nonneg U)
    apply (le_div_iff₀ hQp).mpr
    exact (mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le).trans (by
      change Real.exp (L^c)/4*(Real.exp (L^c)/4) ≤ W at hw
      nlinarith only [hw])
  have he1 : 1 ≤ Real.exp (L^c) := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hscale : L*((x*W)/(W/Q)) = x*L^(a+1) := by
    rw [Real.rpow_add hLp, Real.rpow_one]
    change L*((x*W)/(W/Q)) = x*(Q*L)
    field_simp [hW0.ne', hQp.ne']
  refine ⟨?_,?_,hQ1,hHlo,he1.trans hHlo,?_,hscale⟩
  · exact le_mul_of_one_le_right hx0.le hW1
  · calc
      _ ≤ x*x^ε := mul_le_mul_of_nonneg_left hWupper hx0.le
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  · exact (div_le_self hW0.le hQ1).trans (le_mul_of_one_le_left hW0.le hx)

end
end ArtinMatthews
