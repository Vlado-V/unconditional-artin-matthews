module

public import ArtinMatthews.ProbeEulerLocalBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

noncomputable section

/-- The two manuscript regions, each enlarged by `10^-5` in every coordinate. -/
def probeEulerRegion (x w z : ℝ) : Prop :=
  (99799 / 100000 ≤ x ∧ 299 / 100000 ≤ w ∧ 39999 / 100000 ≤ z) ∨
  (99799 / 100000 ≤ x ∧ 94999 / 100000 ≤ w ∧ 15999 / 100000 ≤ z)

theorem probeEulerRegion_individual {x w z : ℝ} (h : probeEulerRegion x w z) :
    299 / 100000 ≤ x ∧ 299 / 100000 ≤ w ∧ 299 / 100000 ≤ 6 * z ∧
      299 / 100000 ≤ 6 * x + 6 * z - 4 := by
  rcases h with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem probeEulerRegion_errors {x w z : ℝ} (h : probeEulerRegion x w z) :
    1 + 1 / 4000 ≤ x + w ∧ 1 + 1 / 4000 ≤ x + 6 * z ∧
      1 + 1 / 4000 ≤ w + 6 * z ∧ 1 + 1 / 4000 ≤ x + w + 6 * z - 1 ∧
      1 + 1 / 4000 ≤ 6 * x + 6 * z - 4 := by
  rcases h with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

def probeLocalV (Q : ℝ) (z : ℂ) : ℂ := (Q : ℂ) ^ (-(6 * z))
def probeLocalW (Q : ℝ) (a w : ℂ) : ℂ := a * (Q : ℂ) ^ (-w)
def probeLocalD (Q : ℝ) (b x : ℂ) : ℂ := b * (Q : ℂ) ^ (-x)
def probeLocalE (Q : ℝ) (c x z : ℂ) : ℂ :=
  c * (Q : ℂ) ^ (4 - 6 * x - 6 * z)

def probeGoodPrimeCorrection (Q : ℝ) (a b c x w z : ℂ) : ℂ :=
  probeGoodLocalCorrection (Q : ℂ) (probeLocalV Q z) (probeLocalW Q a w)
    (probeLocalD Q b x) (probeLocalE Q c x z)

theorem probeLocalV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖probeLocalV Q z‖ = Q ^ (-(6 * z.re)) := by
  rw [probeLocalV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  congr 1
  simp

theorem probeLocalW_norm_le (Q : ℝ) (hQ : 0 < Q) (a w : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖probeLocalW Q a w‖ ≤ Q ^ (-w.re) := by
  rw [probeLocalW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) ha

theorem probeLocalD_norm_le (Q : ℝ) (hQ : 0 < Q) (b x : ℂ) (hb : ‖b‖ ≤ 1) :
    ‖probeLocalD Q b x‖ ≤ Q ^ (-x.re) :=
  probeLocalW_norm_le Q hQ b x hb

theorem probeLocalE_norm_le (Q : ℝ) (hQ : 0 < Q) (c x z : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖probeLocalE Q c x z‖ ≤ Q ^ (-(6 * x.re + 6 * z.re - 4)) := by
  unfold probeLocalE
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have hr : (4 - 6 * x - 6 * z).re = -(6 * x.re + 6 * z.re - 4) := by
    simp
    ring
  rw [hr]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hc

theorem probe_rpow_product_le {Q u v t : ℝ} (hQ : 1 ≤ Q) (ht : t ≤ u + v) :
    Q ^ (-u) * Q ^ (-v) ≤ Q ^ (-t) := by
  rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hQ)]
  exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)

theorem probeGoodPrimeCorrection_norm_sub_one_le (Q : ℝ) (hQ : 1 ≤ Q)
    (hsmall : Q ^ (-(299 / 100000 : ℝ)) ≤ 1 / 2)
    (a b c x w z : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hregion : probeEulerRegion x.re w.re z.re) :
    ‖probeGoodPrimeCorrection Q a b c x w z - 1‖ ≤
      160 * Q ^ (-(1 + 1 / 4000 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hnQ : ‖(Q : ℂ)‖ = Q := by simp [abs_of_pos hQ0]
  obtain ⟨hx, hw, hv, he⟩ := probeEulerRegion_individual hregion
  obtain ⟨hdw, hdv, hwv, hprod, he'⟩ := probeEulerRegion_errors hregion
  have hvn : ‖probeLocalV Q z‖ ≤ Q ^ (-(6 * z.re)) := (probeLocalV_norm Q hQ0 z).le
  have hwn := probeLocalW_norm_le Q hQ0 a w ha
  have hdn := probeLocalD_norm_le Q hQ0 b x hb
  have hen := probeLocalE_norm_le Q hQ0 c x z hc
  have hhalf {y t : ℝ} (hy : y ≤ Q ^ (-t)) (ht : 299 / 100000 ≤ t) : y ≤ 1 / 2 :=
    (hy.trans (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))).trans hsmall
  have hbase := probeGoodLocalCorrection_norm_sub_one_le (Q : ℂ)
    (probeLocalV Q z) (probeLocalW Q a w) (probeLocalD Q b x) (probeLocalE Q c x z)
    (by rwa [hnQ]) (hhalf hvn hv) (hhalf hwn hw) (hhalf hdn hx) (hhalf hen he)
  rw [hnQ] at hbase
  have h1 : ‖probeLocalD Q b x‖ * ‖probeLocalW Q a w‖ ≤ Q ^ (-(1 + 1 / 4000 : ℝ)) :=
    (mul_le_mul hdn hwn (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)).trans
      (probe_rpow_product_le hQ hdw)
  have h2 : ‖probeLocalD Q b x‖ * ‖probeLocalV Q z‖ ≤ Q ^ (-(1 + 1 / 4000 : ℝ)) :=
    (mul_le_mul hdn hvn (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)).trans
      (probe_rpow_product_le hQ hdv)
  have h3 : ‖probeLocalW Q a w‖ * ‖probeLocalV Q z‖ ≤ Q ^ (-(1 + 1 / 4000 : ℝ)) :=
    (mul_le_mul hwn hvn (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)).trans
      (probe_rpow_product_le hQ hwv)
  have h4 : Q * ‖probeLocalD Q b x‖ * ‖probeLocalW Q a w‖ * ‖probeLocalV Q z‖ ≤
      Q ^ (-(1 + 1 / 4000 : ℝ)) := by
    calc
      _ ≤ Q * Q ^ (-x.re) * Q ^ (-w.re) * Q ^ (-(6 * z.re)) := by gcongr
      _ = Q ^ (-(x.re + w.re + 6 * z.re - 1)) := by
        nth_rw 1 [← Real.rpow_one Q]
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0,
          ← Real.rpow_add hQ0]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have h5 : ‖probeLocalE Q c x z‖ ≤ Q ^ (-(1 + 1 / 4000 : ℝ)) :=
    hen.trans (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))
  unfold probeGoodPrimeCorrection
  linarith

theorem probeGoodPrimeCorrection_eventually :
    ∀ᶠ Q : ℝ in Filter.atTop, ∀ (a b c x w z : ℂ),
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → probeEulerRegion x.re w.re z.re →
      ‖probeGoodPrimeCorrection Q a b c x w z - 1‖ ≤
        160 * Q ^ (-(1 + 1 / 4000 : ℝ)) := by
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 299 / 100000)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hsmall] with Q hQ hs
  exact fun a b c x w z ha hb hc hregion =>
    probeGoodPrimeCorrection_norm_sub_one_le Q hQ hs.le a b c x w z ha hb hc hregion

theorem probeGoodPrimeCorrection_eventually_ne_zero :
    ∀ᶠ Q : ℝ in Filter.atTop, ∀ (a b c x w z : ℂ),
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → probeEulerRegion x.re w.re z.re →
      probeGoodPrimeCorrection Q a b c x w z ≠ 0 := by
  have hdecay := ((tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 1 + 1 / 4000)).const_mul 160).eventually
      (gt_mem_nhds (by norm_num : (160 : ℝ) * 0 < 1 / 2))
  filter_upwards [probeGoodPrimeCorrection_eventually, hdecay] with Q hQ hs
  intro a b c x w z ha hb hc hregion hz
  have h := hQ a b c x w z ha hb hc hregion
  rw [hz, zero_sub, norm_neg, norm_one] at h
  linarith

end

end ArtinMatthews
