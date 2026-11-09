module

public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source memory limit absorbs the maximal store count and
the doubled positive word cost at the growing moment length. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantSignedSourceMemoryTail_budget_eventually
    (storePerGroup : ℕ) (C₀ Cv Cₐ A : ℝ)
    (hC₀ : 0 ≤ C₀) (hCv : 0 ≤ Cv) (hCₐ : 0 ≤ Cₐ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ s : ℕ, (s : ℝ) ≤ C₀ * Real.log (Real.log x) →
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      let B := giantSignedSourceMemoryLimit L
      2 * (L ^ Cv) ^ (n+1) * (L ^ Cₐ) ^ n /
          (2 : ℝ) ^ (B - storePerGroup*s*n) ≤ (L ^ (-A)) ^ n := by
  let K := 1 + 5*Cv + 4*Cₐ + 4*A + 4*(storePerGroup : ℝ)*C₀*Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlimit : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog : ∀ᶠ L : ℝ in atTop, Real.log L / L < Real.log 2 / K :=
    hlimit.eventually (Iio_mem_nhds (div_pos hlog2 hK))
  filter_upwards [Real.tendsto_log_atTop.eventually hlog,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x hx hL2
  intro s hs
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let B := giantSignedSourceMemoryLimit L
  let stores := storePerGroup*s*n
  change 2 * (L ^ Cv) ^ (n+1) * (L ^ Cₐ) ^ n / (2 : ℝ) ^ (B-stores) ≤ (L ^ (-A)) ^ n
  have hL : 2 ≤ L := hL2
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hn : (n : ℝ) ≤ 4 * L := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hp
    exact (giantTwoSidedSourceMomentLength_le (x := x) hL1).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hn1 : ((n+1 : ℕ) : ℝ) ≤ 5 * L := by
    push_cast
    linarith
  have hstores : (stores : ℝ) ≤ 4 * (storePerGroup : ℝ) * C₀ * L * Real.log L := by
    have hmul : (s : ℝ) * (n : ℝ) ≤ (C₀ * Real.log L) * (4 * L) :=
      mul_le_mul hs hn (Nat.cast_nonneg _) (mul_nonneg hC₀ hlogL)
    change ((storePerGroup*s*n : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ = (storePerGroup : ℝ) * ((s : ℝ) * (n : ℝ)) := by ring
      _ ≤ (storePerGroup : ℝ) * ((C₀ * Real.log L) * (4*L)) :=
        mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcap : L ^ 2 ≤ (B : ℝ) := Nat.le_ceil _
  have hremain : (B : ℝ) ≤ ((B-stores : ℕ) : ℝ) + (stores : ℝ) := by
    exact_mod_cast (show B ≤ B-stores+stores by omega)
  have hKlog : K * (L * Real.log L) ≤ Real.log 2 * L ^ 2 := by
    have he := (div_le_iff₀ hL0).mp hx.le
    have hh := mul_le_mul_of_nonneg_left he hK.le
    have hid : K * (Real.log 2 / K * L) = Real.log 2 * L := by field_simp
    rw [hid] at hh
    nlinarith only [mul_le_mul_of_nonneg_right hh hL0.le]
  have hconst : Real.log 2 ≤ L * Real.log L :=
    (Real.log_le_log (by norm_num) hL).trans (le_mul_of_one_le_left hlogL hL1)
  have hsum : Real.log 2 + ((n+1 : ℕ) : ℝ) * (Cv * Real.log L) +
      (n : ℝ) * (Cₐ * Real.log L) + (n : ℝ) * (A * Real.log L) +
      (stores : ℝ) * Real.log 2 ≤ Real.log 2 * L ^ 2 := by
    refine le_trans ?_ hKlog
    dsimp [K]
    nlinarith only [hconst,
      mul_le_mul_of_nonneg_right hn1 (mul_nonneg hCv hlogL),
      mul_le_mul_of_nonneg_right hn (mul_nonneg hCₐ hlogL),
      mul_le_mul_of_nonneg_right hn (mul_nonneg hA hlogL),
      mul_le_mul_of_nonneg_right hstores hlog2.le]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_rpow hL0]
  have hb := mul_le_mul_of_nonneg_left (hcap.trans hremain) hlog2.le
  nlinarith only [hsum, hb]

end
end ArtinMatthews
