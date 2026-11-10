module

public import ArtinMatthews.GiantFixedResidueSieve
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import ArtinMatthews.GiantFixedResidueEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cancellation of the two positive fixed-residue rough main terms.
The model mean of the marking array cancels before taking the large-depth
limit, leaving the original totient and sieve exponent. -/
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology
noncomputable section

theorem giantFixedResidueProgressionDiscrepancy_nonneg (M a : ℕ) (H : ℕ → ℝ) (μ : ℝ)
    (Φ : ℝ → ℝ) (T x : ℝ) (R : ℕ) :
    0≤giantFixedResidueProgressionDiscrepancy M a H μ Φ T x R :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem giantFixedResidueRoughSum_centered (M a : ℕ) (F H : ℕ → ℝ) (C : ℝ)
    (Φ : ℝ → ℝ) (T x γ : ℝ) :
    giantFixedResidueRoughSum M a (fun u => (F u - C) * H u) Φ T x γ =
      giantFixedResidueRoughSum M a (fun u => F u * H u) Φ T x γ -
        C * giantFixedResidueRoughSum M a H Φ T x γ := by
  classical
  unfold giantFixedResidueRoughSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem giantFixedResidue_centered_rough_sieve_bound (M a : ℕ) (F H : ℕ → ℝ) (C μ : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hΦ : ∀ t, 0 ≤ Φ t) (hF : ∀ u, 0 ≤ F u) (hH : ∀ u, 0 ≤ H u)
    (hC : 0 ≤ C) (hM : 0 ≤ μ) (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    |giantFixedResidueRoughSum M a (fun u => (F u - C) * H u) Φ T x γ| ≤
      2 * C * (x * (∫ t in Set.Ioc 0 T, Φ t) * μ) *
        (giantFixedResidueEuler M (x ^ γ)/(M:ℝ)) * Real.exp (-(m : ℝ) / 2) +
      giantFixedResidueProgressionDiscrepancy M a (fun u => F u * H u) (C * μ) Φ T x ⌊x ^ c⌋₊ +
      C * giantFixedResidueProgressionDiscrepancy M a H μ Φ T x ⌊x ^ c⌋₊ := by
  let A := giantFixedResidueRoughSum M a (fun u => F u * H u) Φ T x γ
  let B := giantFixedResidueRoughSum M a H Φ T x γ
  let X := (x * (∫ t in Set.Ioc 0 T, Φ t) * μ) * (giantFixedResidueEuler M (x ^ γ)/(M:ℝ))
  have h₀ := giantFixedResidue_rough_sieve_progression_bridge M a H μ Φ T x γ c m hx hΦ hH hM hcut hm hlevel
  have h₁ := giantFixedResidue_rough_sieve_progression_bridge M a (fun u => F u * H u) (C * μ)
    Φ T x γ c m hx hΦ (fun u => mul_nonneg (hF u) (hH u)) (mul_nonneg hC hM) hcut hm hlevel
  have hX : ((x * (∫ t in Set.Ioc 0 T, Φ t) * (C * μ))/(M:ℝ)) *
      giantFixedResidueEuler M (x ^ γ) = C * X := by dsimp [X]; ring
  have hX₀ : ((x * (∫ t in Set.Ioc 0 T, Φ t) * μ)/(M:ℝ)) *
      giantFixedResidueEuler M (x ^ γ) = X := by dsimp [X]; ring
  rw [hX] at h₁
  rw [hX₀] at h₀
  have htri : |A - C * B| ≤ |A - C * X| + C * |B - X| := by
    calc
      _ = |(A - C * X) - C * (B - X)| := by congr 1; ring
      _ ≤ |A - C * X| + |C * (B - X)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hC]
  rw [giantFixedResidueRoughSum_centered]
  apply htri.trans
  calc
    _ ≤ (C * X * Real.exp (-(m : ℝ) / 2) +
        giantFixedResidueProgressionDiscrepancy M a (fun u => F u * H u) (C * μ) Φ T x ⌊x ^ c⌋₊) +
        C * (X * Real.exp (-(m : ℝ) / 2) + giantFixedResidueProgressionDiscrepancy M a H μ Φ T x ⌊x ^ c⌋₊) :=
      add_le_add h₁ (mul_le_mul_of_nonneg_left h₀ hC)
    _ = _ := by dsimp [X]; ring

theorem giantFixedResidue_centered_rough_normalized_bound (M a : ℕ) (F H : ℕ → ℝ) (C μ : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 < x) (hΦ : ∀ t, 0 ≤ Φ t) (hF : ∀ u, 0 ≤ F u) (hH : ∀ u, 0 ≤ H u)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) {v : ℝ} (hv : 0 < v) (hM : v ≤ μ)
    (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    Real.log x / (x * μ) * |giantFixedResidueRoughSum M a (fun u => (F u - C) * H u) Φ T x γ| ≤
      2 * (∫ t in Set.Ioc 0 T, Φ t) * (Real.log x * (giantFixedResidueEuler M (x ^ γ)/(M:ℝ))) *
        Real.exp (-(m : ℝ) / 2) +
      (Real.log x / x *
        (giantFixedResidueProgressionDiscrepancy M a (fun u => F u * H u) (C * μ) Φ T x ⌊x ^ c⌋₊ +
          giantFixedResidueProgressionDiscrepancy M a H μ Φ T x ⌊x ^ c⌋₊)) / v := by
  let DF := giantFixedResidueProgressionDiscrepancy M a (fun u => F u * H u) (C * μ) Φ T x ⌊x ^ c⌋₊
  let DH := giantFixedResidueProgressionDiscrepancy M a H μ Φ T x ⌊x ^ c⌋₊
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let E := (giantFixedResidueEuler M (x ^ γ)/(M:ℝ))
  let d := Real.exp (-(m : ℝ) / 2)
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < μ := hv.trans_le hM
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hI : 0 ≤ I := integral_nonneg hΦ
  have hE : 0 ≤ E := div_nonneg (giantFixedResidueEuler_pos M _).le (Nat.cast_nonneg M)
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hDF : 0 ≤ DF := giantFixedResidueProgressionDiscrepancy_nonneg _ _ _ _ _ _ _ _
  have hDH : 0 ≤ DH := giantFixedResidueProgressionDiscrepancy_nonneg _ _ _ _ _ _ _ _
  have hfinite := giantFixedResidue_centered_rough_sieve_bound M a F H C μ Φ T x γ c m hx.le
    hΦ hF hH hC0 hM0.le hcut hm hlevel
  have hscale : 0 ≤ Real.log x / (x * μ) := div_nonneg hlog.le (mul_pos hx0 hM0).le
  have hmain : Real.log x / (x * μ) * (2 * C * (x * I * μ) * E * d) ≤
      2 * I * (Real.log x * E) * d := by
    calc
      _ = 2 * C * I * (Real.log x * E) * d := by field_simp [hx0.ne', hM0.ne']
      _ ≤ 2 * 1 * I * (Real.log x * E) * d := by gcongr
      _ = _ := by ring
  have herror : Real.log x / (x * μ) * (DF + C * DH) ≤ (Real.log x / x * (DF + DH)) / v := by
    calc
      _ = (Real.log x / x) * ((DF + C * DH) / μ) := by ring
      _ ≤ (Real.log x / x) * ((DF + DH) / v) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hlog.le hx0.le)
        apply div_le_div₀ (add_nonneg hDF hDH) _ hv hM
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ Real.log x / (x * μ) * (2 * C * (x * I * μ) * E * d + DF + C * DH) :=
      mul_le_mul_of_nonneg_left hfinite hscale
    _ = Real.log x / (x * μ) * (2 * C * (x * I * μ) * E * d) +
        Real.log x / (x * μ) * (DF + C * DH) := by ring
    _ ≤ _ := add_le_add hmain herror

theorem giantFixedResidue_centered_rough_asymptotic (M a : ℕ) (hMpos : 0 < M)
    (F H : ℝ → ℕ → ℝ) (C μ : ℝ → ℝ) (Φ : ℝ → ℝ) (T γ c : ℝ) (m : ℕ)
    (hΦ : ∀ t, 0 ≤ Φ t)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ F x u)
    (hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ H x u)
    (hC : ∀ᶠ x : ℝ in atTop, 0 ≤ C x ∧ C x ≤ 1)
    {v : ℝ} (hv : 0 < v) (hM : ∀ᶠ x : ℝ in atTop, v ≤ μ x)
    (hγ : 0 < γ) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (hprogF : (fun x : ℝ => giantFixedResidueProgressionDiscrepancy M a (fun u => F x u * H x u)
      (C x * μ x) Φ T x ⌊x ^ c⌋₊) =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))))
    (hprogH : (fun x : ℝ => giantFixedResidueProgressionDiscrepancy M a (H x) (μ x) Φ T x ⌊x ^ c⌋₊)
      =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-(1 : ℝ))))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x / (x * μ x) *
          |giantFixedResidueRoughSum M a (fun u => (F x u - C x) * H x u) Φ T x γ| ≤
        2 * (∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant) / (γ*(M.totient:ℝ)) *
          Real.exp (-(m : ℝ) / 2) + η := by
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let B := 2 * I * Real.exp (-Real.eulerMascheroniConstant) / (γ*(M.totient:ℝ)) * Real.exp (-(m : ℝ) / 2)
  let DF (x : ℝ) := giantFixedResidueProgressionDiscrepancy M a (fun u => F x u * H x u)
    (C x * μ x) Φ T x ⌊x ^ c⌋₊
  let DH (x : ℝ) := giantFixedResidueProgressionDiscrepancy M a (H x) (μ x) Φ T x ⌊x ^ c⌋₊
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
  have hmain := ((giantFixedResidueEuler_power_log_tendsto M hMpos hγ).const_mul (2 * I)).mul_const
    (Real.exp (-(m : ℝ) / 2))
  have hlimit : Tendsto (fun x : ℝ =>
      2 * I * (Real.log x * (giantFixedResidueEuler M (x ^ γ)/(M:ℝ))) * Real.exp (-(m : ℝ) / 2) +
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
  exact (giantFixedResidue_centered_rough_normalized_bound M a (F x) (H x) (C x) (μ x) Φ T x γ c m
    hx hΦ hFx hHx hCx.1 hCx.2 hv hMx hcut hm hlevel).trans hs.le

end
end ArtinMatthews
