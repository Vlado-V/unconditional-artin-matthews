module

public import ArtinMatthews.SpectralPeterssonHolomorphic
public import ArtinMatthews.SpectralPeterssonParabolicUnfold
public import Mathlib.Analysis.Normed.Group.Tannery


set_option backward.privateInPublic true
@[expose] public section

/-! The true-width Poincare sum vanishes at every cusp. The period-one
holomorphic chart therefore has genuine exponential decay. -/

noncomputable section
open UpperHalfPlane Set Filter Matrix
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem spectralHolomorphicCuspSeed_zeroAtImInfty (m : ℕ+) :
    IsZeroAtImInfty (spectralHolomorphicCuspSeed (m : ℕ)) := by
  change Tendsto _ atImInfty (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [spectralHolomorphicCuspSeed_norm]
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr m.property
  have hμ : -(2*Real.pi*(m : ℝ)) < 0 := neg_lt_zero.mpr (by positivity)
  have hIm : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have h := Real.tendsto_exp_atBot.comp ((tendsto_id.const_mul_atTop_of_neg hμ).comp hIm)
  simpa only [Function.comp_def,id_eq,neg_mul] using h

theorem spectralHolomorphicSeedSlash_zeroAtImInfty (k : ℕ) (hk : 0 < k) (m : ℕ+)
    (G : SL(2, ℝ)) :
    IsZeroAtImInfty (spectralHolomorphicSlash k G (spectralHolomorphicCuspSeed (m : ℕ))) := by
  change Tendsto _ atImInfty (𝓝 0)
  by_cases hC : G 1 0 = 0
  · have hG : Tendsto (fun z : UpperHalfPlane => G • z) atImInfty atImInfty := by
      change Tendsto (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ G • z)
        atImInfty atImInfty
      apply UpperHalfPlane.tendsto_smul_atImInfty
      simpa using hC
    rw [funext (spectralHolomorphicSlash_apply k G (spectralHolomorphicCuspSeed (m : ℕ)))]
    simp only [hC,Complex.ofReal_zero,zero_mul,zero_add]
    have hseed : Tendsto (spectralHolomorphicCuspSeed (m : ℕ)) atImInfty (𝓝 0) :=
      spectralHolomorphicCuspSeed_zeroAtImInfty m
    simpa only [zero_div,Function.comp_def] using (hseed.comp hG).div_const (((G 1 1 : ℝ) : ℂ)^k)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hCpos : 0 < |G 1 0| := abs_pos.mpr hC
    have hIm : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
    have ha : Tendsto (fun z : UpperHalfPlane => |G 1 0| * z.im) atImInfty atTop :=
      (tendsto_id.const_mul_atTop hCpos).comp hIm
    have hinv : Tendsto (fun z : UpperHalfPlane => (|G 1 0| * z.im)⁻¹) atImInfty (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ha
    have hpow : Tendsto (fun z : UpperHalfPlane => 1/(|G 1 0| * z.im)^k) atImInfty (𝓝 0) := by
      simpa only [zero_pow hk.ne',one_div,inv_pow] using hinv.pow k
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_ hpow
    apply Eventually.of_forall
    intro z
    let D := ((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ)
    have hD : |G 1 0| * z.im ≤ ‖D‖ := by
      simpa only [D,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        UpperHalfPlane.coe_im,zero_mul,add_zero,abs_mul,abs_of_pos z.im_pos] using
        Complex.abs_im_le_norm D
    rw [spectralHolomorphicSlash_apply,norm_div,norm_pow]
    change ‖spectralHolomorphicCuspSeed (m : ℕ) (G • z)‖/‖D‖^k ≤ _
    calc
      _ ≤ 1/‖D‖^k := div_le_div_of_nonneg_right
        (spectralHolomorphicCuspSeed_norm_le_one (m : ℕ) _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one
        (pow_pos (mul_pos hCpos z.im_pos) _)
        (pow_le_pow_left₀ (mul_nonneg hCpos.le z.im_pos.le) hD _)

theorem gamma0PeterssonPoincareChart_zeroAtImInfty (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m : ℕ+) :
    IsZeroAtImInfty (gamma0PeterssonPoincareChart N b a k (m : ℕ)) := by
  let S (z : UpperHalfPlane) := realTranslation (spectralPeterssonStripLift z.re : ℝ) • z
  have hSIm (z : UpperHalfPlane) : (S z).im = z.im := realTranslation_im_smul _ _
  have hSRe (z : UpperHalfPlane) : (S z).re ∈ Ioc (0 : ℝ) 1 := by
    dsimp only [S]
    rw [realTranslation_re_smul]
    exact spectralPeterssonStripLift_mem z.re
  have hIm : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hS : Tendsto S atImInfty atImInfty := by
    change Tendsto S atImInfty (comap UpperHalfPlane.im atTop)
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def,hSIm] using hIm
  let w := (gamma0CuspTrueWidth N b : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  let u (p : Gamma0PeterssonPositiveRow N b a) := gamma0PeterssonUniformRowBound N b a k w w hw p.val
  have hu : Summable u := (gamma0PeterssonUniformRowBound_summable N b a k hk w w hw).subtype
    {p | gamma0PeterssonRowPositive p}
  let f (z : UpperHalfPlane) (p : Gamma0PeterssonPositiveRow N b a) :=
    gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val (S z)
  have hlim (p : Gamma0PeterssonPositiveRow N b a) :
      Tendsto (f · p) atImInfty (𝓝 0) := by
    have h : Tendsto (gamma0PeterssonSignedSummand N b a k (m : ℕ) p.val) atImInfty (𝓝 0) :=
      spectralHolomorphicSeedSlash_zeroAtImInfty k (by omega) m _
    exact h.comp hS
  have hB : ∀ᶠ z : UpperHalfPlane in atImInfty, ∀ p, ‖f z p‖ ≤ u p := by
    filter_upwards [(tendsto_atTop.mp hIm) 1] with z hz
    intro p
    apply gamma0PeterssonSignedSummand_uniform_le
    unfold gamma0PeterssonWidthDilation verticalStrip
    simp only [mem_ofPred_eq,cuspWidthDilation_re_smul,cuspWidthDilation_im_smul]
    change |w*(S z).re| ≤ w ∧ w ≤ w*(S z).im
    have h := hSRe z
    rw [abs_of_nonneg (mul_nonneg hw.le h.1.le),hSIm]
    exact ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left h.2 hw.le,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hw.le⟩
  have htotal : Tendsto (fun z => ∑' p, f z p) atImInfty (𝓝 0) := by
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence (g := fun _ => (0 : ℂ)) hu hlim hB
  change Tendsto _ atImInfty (𝓝 0)
  refine htotal.congr ?_
  intro z
  change gamma0PeterssonPoincareChart N b a k (m : ℕ) (S z) =
    gamma0PeterssonPoincareChart N b a k (m : ℕ) z
  have h := congrFun (gamma0PeterssonPoincareChart_slash_translation N b a k (m : ℕ)
    hk hEven (spectralPeterssonStripLift z.re)) z
  rw [spectralHolomorphicSlash_apply] at h
  simpa [S,realTranslation] using h

theorem gamma0PeterssonPoincareChart_exponential_decay (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m : ℕ+) :
    gamma0PeterssonPoincareChart N b a k (m : ℕ) =O[atImInfty]
      fun z => Real.exp (-(2*Real.pi*z.im)) := by
  have hz := gamma0PeterssonPoincareChart_zeroAtImInfty N b a k hk hEven m
  simpa only [div_one,neg_mul] using
    hz.exp_decay_atImInfty (show (0 : ℝ) < 1 by norm_num)
      (gamma0PeterssonPoincareChart_periodic N b a k (m : ℕ) hk hEven)
      (gamma0PeterssonPoincareChart_mdifferentiable N b a k (m : ℕ) hk)
      hz.isBoundedAtImInfty

end ArtinMatthews
