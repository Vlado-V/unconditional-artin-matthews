module

public import ArtinMatthews.GiantRoughNormalized


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized centered rough-sieve estimate with exact Mertens constant. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

theorem marked_centered_rough_asymptotic
    (F H : ℝ → ℕ → ℝ) (C M : ℝ → ℝ) (Φ : ℝ → ℝ) (T γ c : ℝ) (m : ℕ)
    (hΦ : ∀ t, 0 ≤ Φ t)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ F x u)
    (hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ H x u)
    (hC : ∀ᶠ x : ℝ in atTop, 0 ≤ C x ∧ C x ≤ 1)
    {v : ℝ} (hv : 0 < v) (hM : ∀ᶠ x : ℝ in atTop, v ≤ M x)
    (hγ : 0 < γ) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (hprogF : (fun x : ℝ => markedProgressionDiscrepancy (fun u => F x u * H x u)
      (C x * M x) Φ T x ⌊x ^ c⌋₊) =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))))
    (hprogH : (fun x : ℝ => markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊)
      =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x / (x * M x) *
          |markedRoughPredecessorSum (fun u => (F x u - C x) * H x u) Φ T x γ| ≤
        2 * (∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant) / γ *
          Real.exp (-(m : ℝ) / 2) + η := by
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let B := 2 * I * Real.exp (-Real.eulerMascheroniConstant) / γ * Real.exp (-(m : ℝ) / 2)
  let DF (x : ℝ) := markedProgressionDiscrepancy (fun u => F x u * H x u)
    (C x * M x) Φ T x ⌊x ^ c⌋₊
  let DH (x : ℝ) := markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊
  have hEF : Tendsto (fun x : ℝ => Real.log x / x * DF x) atTop (𝓝 0) := by
    apply hprogF.tendsto_div_nhds_zero.congr'
    filter_upwards [] with x
    simp only [Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hEH : Tendsto (fun x : ℝ => Real.log x / x * DH x) atTop (𝓝 0) := by
    apply hprogH.tendsto_div_nhds_zero.congr'
    filter_upwards [] with x
    simp only [Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hmain := ((markedSieveEulerProduct_power_log_tendsto hγ).const_mul (2 * I)).mul_const
    (Real.exp (-(m : ℝ) / 2))
  have hlimit : Tendsto (fun x : ℝ =>
      2 * I * (Real.log x * markedSieveEulerProduct (x ^ γ)) * Real.exp (-(m : ℝ) / 2) +
        (Real.log x / x * (DF x + DH x)) / v) atTop (𝓝 B) := by
    convert hmain.add ((hEF.add hEH).div_const v) using 1
    · ext x
      ring
    · dsimp [B]
      ring
  have hsmall := hlimit.eventually (gt_mem_nhds (lt_add_of_pos_right B hη))
  filter_upwards [hF, hH, hC, hM, hsmall, eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop (2 : ℝ))]
    with x hFx hHx hCx hMx hs hx hpow
  have hcut : 2 ≤ ⌊x ^ γ⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg (by linarith : 0 ≤ x) γ)).mpr (by exact_mod_cast hpow)
  exact (marked_centered_rough_normalized_bound (F x) (H x) (C x) (M x) Φ T x γ c m
    hx hΦ hFx hHx hCx.1 hCx.2 hv hMx hcut hm hlevel).trans hs.le

end ArtinMatthews
