module

public import ArtinMatthews.SourceKPJacquetFrequencyCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Finite shell estimates at the negative residue exponent. The
self-dual integer-ball mass is retained at every finite place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical MeasureTheory
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "Q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "ν₀" => sourceLocalValuation K P
local notation "μ₀" => sourceLocalSelfDual K P

def sourceKPJacquetOpenEnvelope (x : L) : ℝ := (max 1 ‖x‖) ^ (-(2 / 3) : ℝ)

local notation "F" => sourceKPJacquetOpenEnvelope K P

theorem sourceKPJacquetOpenEnvelope_continuous : Continuous F := by
  apply (continuous_const.max continuous_norm).rpow_const
  intro x
  exact Or.inl (zero_lt_one.trans_le (le_max_left (1 : ℝ) ‖x‖)).ne'

theorem sourceKPJacquet_norm_le_of_ball {x : L} {R : ℤ} (hx : x ∈ B R) : ‖x‖ ≤ Q ^ R := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]
    exact (zpow_pos (sourceLocalNorm_pos K P) R).le
  have he : WithZero.log (ν₀ x) ≤ R := by
    apply WithZero.exp_le_exp.mp
    rw [WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx0)]
    exact hx
  rw [sourceLocalNorm_eq_zpow K P x hx0]
  exact zpow_le_zpow_right₀ (VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P).le he

theorem sourceKPJacquet_shell_norm {x : L} {l : ℕ}
    (hx : x ∈ sourceJacquetValuationShell K P (l : ℤ)) : ‖x‖ = Q ^ l := by
  have hv := (sourceJacquetValuationShell_mem K P (l : ℤ) x).mp hx
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  rw [sourceLocalNorm_eq_zpow K P x hx0, hv, WithZero.log_exp, zpow_natCast]

theorem sourceKPJacquetOpenEnvelope_ball_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∫ x in B (R : ℤ), F x ∂μ₀) ≤ C * (Q ^ (1 / 3 : ℝ)) ^ R := by
  let q := Q ^ (1 / 3 : ℝ)
  have hQ : 1 < Q := VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P
  have hq : 1 < q := Real.one_lt_rpow hQ (by norm_num)
  let μ := (μ₀).real (B 0)
  let A := q / (q - 1)
  have hμ : 0 < μ := sourceLocalBall_volume_pos K P 0
  have hA : 0 < A := div_pos (zero_lt_one.trans hq) (sub_pos.mpr hq)
  have hA1 : 1 ≤ A := (le_div_iff₀ (sub_pos.mpr hq)).mpr (by linarith)
  have hAq : A + q = A * q := by
    dsimp only [A]
    field_simp [(sub_pos.mpr hq).ne']
    ring
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hF := sourceKPJacquetOpenEnvelope_continuous K P
  have hI (n : ℤ) : IntegrableOn F (B n) μ₀ :=
    hF.continuousOn.integrableOn_compact (sourceLocalBall_isCompact K P n)
  have hshell (l : ℕ) :
      (∫ x in sourceJacquetValuationShell K P (l : ℤ), F x ∂μ₀) ≤ μ * q ^ l := by
    let S := sourceJacquetValuationShell K P (l : ℤ)
    have hs : MeasurableSet S := (sourceJacquetValuationShell_isCompact K P _).measurableSet
    have hvol : (μ₀).real S ≤ Q ^ l * μ := by
      calc
        _ ≤ (μ₀).real (B (l : ℤ)) := measureReal_mono (fun _ hx => hx.1)
          (sourceLocalBall_isCompact K P _).measure_ne_top
        _ = _ := by rw [sourceLocalBall_volume_scaling K P, zpow_natCast]
    have hvalue (x : L) (hx : x ∈ S) : F x = (Q ^ l) ^ (-(2 / 3) : ℝ) := by
      rw [sourceKPJacquetOpenEnvelope, sourceKPJacquet_shell_norm K P hx,
        max_eq_right (one_le_pow₀ hQ.le)]
    calc
      _ = ∫ _x in S, (Q ^ l) ^ (-(2 / 3) : ℝ) ∂μ₀ := setIntegral_congr_fun hs hvalue
      _ ≤ Q ^ l * μ * (Q ^ l) ^ (-(2 / 3) : ℝ) := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right hvol (Real.rpow_nonneg (pow_nonneg (sourceLocalNorm_pos K P).le _) _)
      _ = μ * q ^ l := by
        rw [show Q ^ l * μ * (Q ^ l) ^ (-(2 / 3) : ℝ) =
          μ * ((Q ^ l) ^ (-(2 / 3) : ℝ) * Q ^ l) by ring,
          ← Real.rpow_add_one (pow_ne_zero _ (sourceLocalNorm_pos K P).ne')]
        rw [show -(2 / 3 : ℝ) + 1 = 1 / 3 by norm_num,
          ← Real.rpow_pow_comm (sourceLocalNorm_pos K P).le]
  refine ⟨μ * A, mul_pos hμ hA, ?_⟩
  intro R
  change (∫ x in B (R : ℤ), F x ∂μ₀) ≤ μ * A * q ^ R
  induction R with
  | zero =>
    have he : (∫ x in B (0 : ℤ), F x ∂μ₀) = μ := by
      calc
        _ = ∫ _x in B (0 : ℤ), (1 : ℝ) ∂μ₀ := by
          apply setIntegral_congr_fun (sourceLocalBall_isOpen K P _).measurableSet
          intro x hx
          have hx' : ‖x‖ ≤ 1 := by simpa only [zpow_zero] using sourceKPJacquet_norm_le_of_ball K P hx
          rw [sourceKPJacquetOpenEnvelope, max_eq_left hx', Real.one_rpow]
        _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one]
    simp only [Nat.cast_zero, pow_zero, mul_one, he]
    exact le_mul_of_one_le_right hμ.le hA1
  | succ R ih =>
    let S := sourceJacquetValuationShell K P ((R : ℤ) + 1)
    have hS : IsCompact S := sourceJacquetValuationShell_isCompact K P _
    have hd : Disjoint (B (R : ℤ)) S := by
      rw [show S = B ((R : ℤ) + 1) \ B (R : ℤ) by
        unfold S sourceJacquetValuationShell; rw [add_sub_cancel_right]]
      exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
    rw [Nat.cast_succ, sourceJacquetBall_succ K P,
      setIntegral_union hd hS.measurableSet (hI _) (hF.continuousOn.integrableOn_compact hS)]
    have hs := hshell (R + 1)
    rw [Nat.cast_succ] at hs
    calc
      _ ≤ μ * A * q ^ R + μ * q ^ (R + 1) := add_le_add ih hs
      _ = μ * q ^ R * (A + q) := by rw [pow_succ]; ring
      _ = _ := by rw [hAq, pow_succ]; ring

theorem sourceKPJacquetFrequencyRadius_pow_eq (M N : ℕ) (z : Lˣ) (hz : (z : L) ∈ B 0) :
    (Q ^ (1 / 3 : ℝ)) ^ sourceKPJacquetFrequencyRadius K P M N z =
      (Q ^ (1 / 3 : ℝ)) ^ (sourceDifferentExponent K P + 1 + M + N) * ‖(z : L)‖ ^ (-(1 / 3) : ℝ) := by
  let n := WithZero.log (ν₀ (z : L))
  have hn : n ≤ 0 := by
    apply WithZero.exp_le_exp.mp
    rw [show WithZero.exp n = ν₀ (z : L) from WithZero.exp_log ((Valuation.ne_zero_iff _).mpr z.ne_zero)]
    exact hz
  have hr : (sourceKPJacquetFrequencyRadius K P M N z : ℤ) =
      (↑(sourceDifferentExponent K P + 1 + M + N) : ℤ) - n := by
    unfold sourceKPJacquetFrequencyRadius
    push_cast
    change (((sourceDifferentExponent K P : ℤ) + 1 - n).toNat : ℤ) + M + N = _
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hq : 0 < Q ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (sourceLocalNorm_pos K P) _
  rw [← zpow_natCast, hr, zpow_sub₀ hq.ne', zpow_natCast, div_eq_mul_inv,
    Real.rpow_zpow_comm (sourceLocalNorm_pos K P).le,
    ← sourceLocalNorm_eq_zpow K P (z : L) z.ne_zero,
    ← Real.rpow_neg (norm_nonneg (z : L))]

end
end ArtinMatthews
