module

public import ArtinMatthews.GiantRoughCentering


set_option backward.privateInPublic true
@[expose] public section

/-! Normalizing the centered rough sieve by the actual positive model mean.
Its leading constant is independent of the number of marking bands. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

theorem marked_centered_rough_normalized_bound (F H : ℕ → ℝ) (C M : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 < x) (hΦ : ∀ t, 0 ≤ Φ t) (hF : ∀ u, 0 ≤ F u) (hH : ∀ u, 0 ≤ H u)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) {v : ℝ} (hv : 0 < v) (hM : v ≤ M)
    (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    Real.log x / (x * M) * |markedRoughPredecessorSum (fun u => (F u - C) * H u) Φ T x γ| ≤
      2 * (∫ t in Set.Ioc 0 T, Φ t) * (Real.log x * markedSieveEulerProduct (x ^ γ)) *
        Real.exp (-(m : ℝ) / 2) +
      (Real.log x / x *
        (markedProgressionDiscrepancy (fun u => F u * H u) (C * M) Φ T x ⌊x ^ c⌋₊ +
          markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊)) / v := by
  let DF := markedProgressionDiscrepancy (fun u => F u * H u) (C * M) Φ T x ⌊x ^ c⌋₊
  let DH := markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let E := markedSieveEulerProduct (x ^ γ)
  let d := Real.exp (-(m : ℝ) / 2)
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := hv.trans_le hM
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hI : 0 ≤ I := integral_nonneg hΦ
  have hE : 0 ≤ E := (markedSieveEulerProduct_pos _).le
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hDF : 0 ≤ DF := markedProgressionDiscrepancy_nonneg _ _ _ _ _ _
  have hDH : 0 ≤ DH := markedProgressionDiscrepancy_nonneg _ _ _ _ _ _
  have hfinite := marked_centered_rough_sieve_bound F H C M Φ T x γ c m hx.le
    hΦ hF hH hC0 hM0.le hcut hm hlevel
  have hscale : 0 ≤ Real.log x / (x * M) := div_nonneg hlog.le (mul_pos hx0 hM0).le
  have hmain : Real.log x / (x * M) * (2 * C * (x * I * M) * E * d) ≤
      2 * I * (Real.log x * E) * d := by
    calc
      _ = 2 * C * I * (Real.log x * E) * d := by field_simp [hx0.ne', hM0.ne']
      _ ≤ 2 * 1 * I * (Real.log x * E) * d := by gcongr
      _ = _ := by ring
  have herror : Real.log x / (x * M) * (DF + C * DH) ≤ (Real.log x / x * (DF + DH)) / v := by
    calc
      _ = (Real.log x / x) * ((DF + C * DH) / M) := by ring
      _ ≤ (Real.log x / x) * ((DF + DH) / v) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hlog.le hx0.le)
        apply div_le_div₀ (add_nonneg hDF hDH) _ hv hM
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ Real.log x / (x * M) * (2 * C * (x * I * M) * E * d + DF + C * DH) :=
      mul_le_mul_of_nonneg_left hfinite hscale
    _ = Real.log x / (x * M) * (2 * C * (x * I * M) * E * d) +
        Real.log x / (x * M) * (DF + C * DH) := by ring
    _ ≤ _ := add_le_add hmain herror

end ArtinMatthews
