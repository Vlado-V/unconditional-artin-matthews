module

public import ArtinMatthews.MarkedSieveProgressionBridge


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive sieve with the exact Mertens constant. The only
asymptotic input for the weight is its proved progression discrepancy;
the finite prime-sum comparison is derived in the preceding bridge. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

/-- A nonnegative weight with small actual progression discrepancy and
bounded proposed mean satisfies the asymptotic upper sieve inequality. -/
theorem marked_sieve_asymptotic (H : ℝ → ℕ → ℝ) (M : ℝ → ℝ)
    (Φ : ℝ → ℝ) (T γ c B : ℝ) (m : ℕ)
    (hΦ : ∀ t, 0 ≤ Φ t)
    (hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ H x u)
    (hM : ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧ M x ≤ B)
    (hγ : 0 < γ) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (hprog : (fun x : ℝ => markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter
          (fun u => (u + 1).Prime ∧ ⌊x ^ γ⌋₊ < u + 1), Φ ((u : ℝ) / x) * H x u) ≤
        (((∫ t in Set.Ioc 0 T, Φ t) * B * Real.exp (-Real.eulerMascheroniConstant) / γ) *
          (1 + Real.exp (-(m : ℝ) / 2)) + ε) * x / Real.log x := by
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let K := 1 + Real.exp (-(m : ℝ) / 2)
  let C := (I * B * Real.exp (-Real.eulerMascheroniConstant) / γ) * K
  have hI : 0 ≤ I := integral_nonneg hΦ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have herror : Tendsto (fun x : ℝ => Real.log x / x *
      markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊) atTop (𝓝 0) := by
    apply hprog.tendsto_div_nhds_zero.congr'
    filter_upwards [] with x
    simp only [Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hmain := ((markedSieveEulerProduct_power_log_tendsto hγ).const_mul (I * B)).mul_const K
  have hlimit : Tendsto (fun x : ℝ =>
      I * B * (Real.log x * markedSieveEulerProduct (x ^ γ)) * K +
        Real.log x / x * markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊)
      atTop (𝓝 C) := by
    convert hmain.add herror using 1
    dsimp [C]
    ring
  have hsmall := hlimit.eventually (gt_mem_nhds (lt_add_of_pos_right C hε))
  filter_upwards [hH, hM, hsmall, eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop (2 : ℝ))]
    with x hHx hMx hsmallx hx hpow
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hMB : M x ≤ B := hMx.2
  have hcut : 2 ≤ ⌊x ^ γ⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hx0.le γ)).mpr (by exact_mod_cast hpow)
  have hproduct : 0 ≤ markedSieveEulerProduct (x ^ γ) := (markedSieveEulerProduct_pos _).le
  have hfinite := marked_sieve_progression_bridge (H x) (M x) Φ T x γ c m
    hx.le hΦ hHx hMx.1 hcut hm hlevel
  let S := ∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter
    (fun u => (u + 1).Prime ∧ ⌊x ^ γ⌋₊ < u + 1), Φ ((u : ℝ) / x) * H x u
  have hnorm : Real.log x / x * S ≤
      I * B * (Real.log x * markedSieveEulerProduct (x ^ γ)) * K +
        Real.log x / x * markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊ := by
    calc
      _ ≤ Real.log x / x *
          ((x * I * M x) * markedSieveEulerProduct (x ^ γ) * K +
            markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊) :=
        mul_le_mul_of_nonneg_left hfinite (div_nonneg hlog.le hx0.le)
      _ = I * M x * (Real.log x * markedSieveEulerProduct (x ^ γ)) * K +
          Real.log x / x * markedProgressionDiscrepancy (H x) (M x) Φ T x ⌊x ^ c⌋₊ := by
        field_simp
      _ ≤ _ := by gcongr
  have hfrac : (S * Real.log x) / x < C + ε := by
    convert hnorm.trans_lt hsmallx using 1
    ring
  have hresult : S < (C + ε) * x / Real.log x :=
    (lt_div_iff₀ hlog).mpr ((div_lt_iff₀ hx0).mp hfrac)
  exact hresult.le

end ArtinMatthews
