module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Logarithmic integral bounds for finite Fourier kernels

A kernel bounded by its length near the origin and by the reciprocal distance
away from the origin has logarithmic L¹ norm. The integral estimates here are
proved by splitting at the reciprocal length and integrating `1 / t`.
-/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

/-- Integration of the standard constant/reciprocal majorant, with an arbitrary
positive upper endpoint. No logarithmic integral estimate is assumed. -/
theorem integral_le_log_of_constant_reciprocal_bounds
    {g : ℝ → ℝ} {C N L : ℝ} (hg : Continuous g)
    (hN : 0 < N) (hL : 1 / N ≤ L)
    (hflat : ∀ t ∈ Icc 0 (1 / N), g t ≤ C * N)
    (htail : ∀ t ∈ Icc (1 / N) L, g t ≤ C / t) :
    (∫ t in 0..L, g t) ≤ C * (1 + Real.log (L * N)) := by
  have ha : 0 < 1 / N := one_div_pos.mpr hN
  have hLpos : 0 < L := ha.trans_le hL
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume (1 / N) L := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Icc (1 / N) L := by rwa [uIcc_of_le hL] at ht
      exact ne_of_gt (ha.trans_le ht'.1)
    · exact continuous_id.continuousOn
  have hflatInt : (∫ t in 0..(1 / N), g t) ≤ C := by
    calc
      _ ≤ ∫ _t in 0..(1 / N), C * N :=
        intervalIntegral.integral_mono_on ha.le (hg.intervalIntegrable _ _)
          intervalIntegrable_const hflat
      _ = C := by simp [hN.ne']
  have htailInt : (∫ t in (1 / N)..L, g t) ≤ C * Real.log (L * N) := by
    calc
      _ ≤ ∫ t in (1 / N)..L, C * (1 / t) := by
        apply intervalIntegral.integral_mono_on hL (hg.intervalIntegrable _ _) (hinv.const_mul C)
        intro t ht
        simpa only [mul_one_div] using htail t ht
      _ = C * Real.log (L * N) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hLpos]
        simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable 0 (1 / N)) (hg.intervalIntegrable (1 / N) L)]
  nlinarith

/-- The logarithmic bound on a unit interval. -/
theorem integral_le_one_add_log_of_bounds
    {g : ℝ → ℝ} {C N : ℝ} (hg : Continuous g) (hN : 1 ≤ N)
    (hflat : ∀ t ∈ Icc 0 1, g t ≤ C * N)
    (htail : ∀ t ∈ Ioc 0 1, g t ≤ C / t) :
    (∫ t in 0..1, g t) ≤ C * (1 + Real.log N) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have ha : 1 / N ≤ 1 := (div_le_one hNpos).mpr hN
  simpa only [one_mul] using integral_le_log_of_constant_reciprocal_bounds hg hNpos ha
    (fun t ht => hflat t ⟨ht.1, ht.2.trans ha⟩)
    (fun t ht => htail t ⟨(one_div_pos.mpr hNpos).trans_le ht.1, ht.2⟩)

/-- A complex kernel inherits the logarithmic bound from its pointwise norm bounds. -/
theorem integral_norm_le_one_add_log_of_bounds
    {K : ℝ → ℂ} {C N : ℝ} (hK : Continuous K) (hN : 1 ≤ N)
    (hflat : ∀ t ∈ Icc 0 1, ‖K t‖ ≤ C * N)
    (htail : ∀ t ∈ Ioc 0 1, ‖K t‖ ≤ C / t) :
    (∫ t in 0..1, ‖K t‖) ≤ C * (1 + Real.log N) :=
  integral_le_one_add_log_of_bounds hK.norm hN hflat htail

/-- A symmetric period-one kernel can be estimated on the first half-period.
This is the form used after the Dirichlet-kernel pointwise estimate. -/
theorem integral_norm_le_log_of_symmetric_bounds
    {K : ℝ → ℂ} {C N : ℝ} (hK : Continuous K) (hC : 0 ≤ C) (hN : 2 ≤ N)
    (hsymm : ∀ t : ℝ, ‖K (1 - t)‖ = ‖K t‖)
    (hflat : ∀ t ∈ Icc 0 (1 / 2 : ℝ), ‖K t‖ ≤ C * N)
    (htail : ∀ t ∈ Ioc 0 (1 / 2 : ℝ), ‖K t‖ ≤ C / t) :
    (∫ t in 0..1, ‖K t‖) ≤ 2 * C * (1 + Real.log N) := by
  have hNpos : 0 < N := by linarith
  have ha : 1 / N ≤ (1 / 2 : ℝ) := (div_le_div_iff₀ hNpos (by norm_num)).mpr (by linarith)
  have hhalf : (∫ t in 0..(1 / 2 : ℝ), ‖K t‖) ≤ C * (1 + Real.log N) := by
    calc
      _ ≤ C * (1 + Real.log ((1 / 2 : ℝ) * N)) :=
        integral_le_log_of_constant_reciprocal_bounds hK.norm hNpos ha
          (fun t ht => hflat t ⟨ht.1, ht.2.trans ha⟩)
          (fun t ht => htail t ⟨(one_div_pos.mpr hNpos).trans_le ht.1, ht.2⟩)
      _ ≤ C * (1 + Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hlog : Real.log ((1 / 2 : ℝ) * N) ≤ Real.log N :=
          Real.log_le_log (by positivity) (by linarith)
        linarith
  have hright : (∫ t in (1 / 2 : ℝ)..1, ‖K t‖) =
      ∫ t in 0..(1 / 2 : ℝ), ‖K t‖ := by
    have hsub := intervalIntegral.integral_comp_sub_left (fun t => ‖K t‖)
      (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (1 : ℝ)
    norm_num only [sub_half, sub_zero] at hsub
    rw [← hsub]
    simp_rw [hsymm]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hK.norm.intervalIntegrable 0 (1 / 2)) (hK.norm.intervalIntegrable (1 / 2) 1), hright]
  linarith

/-- Reflection and translation do not change the integral of the norm of a
period-one kernel. Continuity is not needed for this identity. -/
theorem integral_norm_sub_eq_of_periodic
    {K : ℝ → ℂ} (hperiod : Function.Periodic K 1) (θ : ℝ) :
    (∫ x in 0..1, ‖K (θ - x)‖) = ∫ x in 0..1, ‖K x‖ := by
  have hnorm : Function.Periodic (fun t => ‖K t‖) 1 :=
    fun t => congrArg norm (hperiod t)
  rw [intervalIntegral.integral_comp_sub_left (fun t => ‖K t‖)]
  simpa using hnorm.intervalIntegral_add_eq (θ - 1) 0

end ArtinMatthews
