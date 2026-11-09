module

public import ArtinMatthews.HeckeIntervalDyadicPower
public import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular


set_option backward.privateInPublic true
@[expose] public section

/-! Removing actual ideal prime powers from the moving interval profile,
with its transition-width loss and a uniform positive power saving. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths

theorem heckeLogIntervalCutoff_norm_le_one {ε u v : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (y : ℝ) : ‖heckeLogIntervalCutoff ε u v y‖ ≤ 1 := by
  unfold heckeLogIntervalCutoff
  split_ifs
  · exact heckeLogIntervalProfile_norm_le_one hε huv _
  · norm_num

theorem heckeInterval_primePolynomial_power (B : ℝ) (hB : 0 ≤ B) :
    ∃ C H₀ : ℝ, 0 < C ∧ 0 < H₀ ∧ ∃ k : ℕ, 2 ≤ k ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      ∀ H : ℝ, H₀ ≤ H → ∀ η : HeckeFamily.Character,
      η.residue ≠ 1 → (η.modulus.absNorm : ℝ) ≤ H →
      ∀ t : ℝ, |t| ≤ H^B →
      ‖HeckePrimeAnnular.primePolynomial η (heckeLogIntervalCutoff ε u v) (2*Real.exp 1) H 0 t‖ ≤
        (C/ε^k)*H^(13/32 : ℝ) := by
  obtain ⟨C, hC, k, hk, hdyadic⟩ := heckeInterval_dyadic_power B hB
  obtain ⟨Ce, hCe, herror⟩ := HeckePrimeAnnular.extraction_bound (1/32) (by norm_num)
  let b := 2*Real.exp 1
  let E := Ce*(max 1 b)^((1/2 : ℝ)+1/32)
  have hE : 0 < E := by dsimp [E]; positivity
  let H₀ := max 5 (Real.exp (2*(|Real.log 1|+|Real.log b|)+1))
  refine ⟨C+E, H₀, by positivity,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) (le_max_left _ _), k, hk, ?_⟩
  intro ε hε hε1 u v hu huv hv H hH η hη hmod t ht
  have hH5 : 5 ≤ H := (le_max_left _ _).trans hH
  have hHp : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hlog : 2*(|Real.log 1|+|Real.log b|)+1 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos _ ) ((le_max_right _ _).trans hH)
    rwa [Real.log_exp] at h
  have hlog1 : 1 ≤ Real.log H := by linarith [abs_nonneg (Real.log 1), abs_nonneg (Real.log b)]
  have hL : 1/Real.log H ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr hlog1⟩
  have hd := hdyadic ε hε hε1 u v hu huv hv H hH5 η hη hmod t ht _ hL
  have he := herror η (heckeLogIntervalCutoff ε u v) 1 b H 0 t 1 (by norm_num)
    hH1 (heckeLogIntervalCutoff_uniform_support hε hε1 hu huv hv) hlog (by norm_num)
    (fun y _ => by simpa only [neg_zero, Real.rpow_zero, mul_one] using
      heckeLogIntervalCutoff_norm_le_one hε huv y)
  have hEwidth : E ≤ E/ε^k := by
    apply (le_div_iff₀ (pow_pos hε k)).mpr
    exact mul_le_of_le_one_right hE.le (pow_le_one₀ hε.le hε1)
  have he' : ‖HeckePrimeAnnular.primePolynomial η (heckeLogIntervalCutoff ε u v) b H 0 t -
      HeckePrimeDyadic.polynomial η
        (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) (1/Real.log H)) H 0 t‖ ≤
      (E/ε^k)*H^(13/32 : ℝ) := by
    rw [norm_sub_rev]
    apply he.trans
    change E*H^(1/32 : ℝ)*1 ≤ _
    rw [mul_one]
    exact mul_le_mul hEwidth (Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num))
      (Real.rpow_nonneg hHp.le _) (by positivity)
  apply (norm_le_insert' _
    (HeckePrimeDyadic.polynomial η
      (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) (1/Real.log H)) H 0 t)).trans
  exact (add_le_add hd he').trans_eq (by ring)

end ArtinMatthews
