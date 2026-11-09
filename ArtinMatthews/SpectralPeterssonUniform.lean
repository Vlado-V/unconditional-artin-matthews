module

public import ArtinMatthews.SpectralPeterssonPoincare
public import Mathlib.Analysis.Normed.Group.FunctionSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform convergence on actual compact subsets of the upper half plane.
The explicit Eisenstein majorant is valid on the full vertical strip. -/

noncomputable section
open UpperHalfPlane Set Filter Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonUniformRowBound (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (A B : ℝ) (hB : 0 < B) (p : Gamma0PeterssonSignedRow N b a) : ℝ :=
  ((gamma0PeterssonWidthRatio N b a)^k)⁻¹*
    (EisensteinSeries.r ⟨⟨A,B⟩,hB⟩^(-(k : ℝ))*‖p.val‖^(-(k : ℝ)))

theorem gamma0PeterssonUniformRowBound_nonneg (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (A B : ℝ) (hB : 0 < B) (p : Gamma0PeterssonSignedRow N b a) :
    0 ≤ gamma0PeterssonUniformRowBound N b a k A B hB p := by
  unfold gamma0PeterssonUniformRowBound
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (gamma0PeterssonWidthRatio_pos N b a).le _))
    (mul_nonneg (Real.rpow_nonneg (EisensteinSeries.r_pos _).le _) (Real.rpow_nonneg (norm_nonneg _) _))

theorem gamma0PeterssonUniformRowBound_summable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (A B : ℝ) (hB : 0 < B) :
    Summable (gamma0PeterssonUniformRowBound N b a k A B hB) := by
  have h : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hs : Summable (fun p : Gamma0PeterssonSignedRow N b a => ‖p.val‖^(-(k : ℝ))) :=
    (EisensteinSeries.summable_one_div_norm_rpow h).comp_injective
      (show Function.Injective (fun p : Gamma0PeterssonSignedRow N b a => p.val) from Subtype.val_injective)
  refine (hs.mul_left (((gamma0PeterssonWidthRatio N b a)^k)⁻¹*
    EisensteinSeries.r ⟨⟨A,B⟩,hB⟩^(-(k : ℝ)))).congr ?_
  intro p
  exact mul_assoc _ _ _

theorem gamma0PeterssonSignedSummand_uniform_le (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (A B : ℝ) (hB : 0 < B) (p : Gamma0PeterssonSignedRow N b a)
    (z : UpperHalfPlane) (hz : gamma0PeterssonWidthDilation N b • z ∈ verticalStrip A B) :
    ‖gamma0PeterssonSignedSummand N b a k m p z‖ ≤ gamma0PeterssonUniformRowBound N b a k A B hB p := by
  refine (gamma0PeterssonSignedSummand_norm_le N b a k m p z).trans ?_
  unfold gamma0PeterssonUniformRowBound
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (pow_nonneg (gamma0PeterssonWidthRatio_pos N b a).le _))
  simpa only [EisensteinSeries.eisSummand,norm_zpow,← Real.rpow_intCast,Int.cast_neg,Int.cast_natCast] using
    EisensteinSeries.summand_bound_of_mem_verticalStrip (Nat.cast_nonneg k) p.val hB hz

theorem spectralHolomorphicSlash_continuous (k : ℕ) (g : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) : Continuous (spectralHolomorphicSlash k g F) := by
  have hg : Continuous (fun z : UpperHalfPlane => g • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z)
    exact continuous_const_smul _
  have hdenom (z : UpperHalfPlane) :
      ((g 1 0 : ℝ) : ℂ)*(z : ℂ)+((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  rw [funext (spectralHolomorphicSlash_apply k g F)]
  exact (hF.comp hg).div (by fun_prop) (fun z => pow_ne_zero _ (hdenom z))

theorem gamma0PeterssonSignedSummand_continuous (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (p : Gamma0PeterssonSignedRow N b a) :
    Continuous (gamma0PeterssonSignedSummand N b a k m p) := by
  unfold gamma0PeterssonSignedSummand gamma0PeterssonMatrixSeed
  apply spectralHolomorphicSlash_continuous
  unfold spectralHolomorphicCuspSeed
  fun_prop

theorem gamma0PeterssonPoincareChart_locallyUniformly (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (k m : ℕ) (hk : 3 ≤ k) :
    TendstoLocallyUniformly (fun s : Finset (Gamma0PeterssonPositiveRow N b a) =>
      fun z => ∑ p ∈ s, gamma0PeterssonSignedSummand N b a k m p.val z)
      (gamma0PeterssonPoincareChart N b a k m) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  let Db := gamma0PeterssonWidthDilation N b
  have hD : Continuous (fun z : UpperHalfPlane => Db • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ Db • z)
    exact continuous_const_smul _
  obtain ⟨A,B,hB,hK'⟩ := subset_verticalStrip_of_isCompact (hK.image hD)
  let u := gamma0PeterssonUniformRowBound N b a k A B hB
  have hu := (gamma0PeterssonUniformRowBound_summable N b a k hk A B hB).subtype
    {p | gamma0PeterssonRowPositive p}
  exact tendstoUniformlyOn_tsum (hu := hu) (fun p z hz =>
    gamma0PeterssonSignedSummand_uniform_le N b a k m A B hB p.val z
      (hK' (mem_image_of_mem _ hz)))

theorem gamma0PeterssonPoincareChart_continuous (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (k m : ℕ) (hk : 3 ≤ k) :
    Continuous (gamma0PeterssonPoincareChart N b a k m) := by
  apply (gamma0PeterssonPoincareChart_locallyUniformly N b a k m hk).continuous
  exact Frequently.of_forall (fun (s : Finset (Gamma0PeterssonPositiveRow N b a)) =>
    continuous_finsetSum s (fun p _ => gamma0PeterssonSignedSummand_continuous N b a k m p.val))

end ArtinMatthews
