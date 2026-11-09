module

public import ArtinMatthews.SpectralEisensteinForcingCusps
public import ArtinMatthews.SpectralEisensteinRemainderL2


set_option backward.privateInPublic true
@[expose] public section

/-! Exact high-cusp values of actual normalized height profiles. Every
nonzero lower row vanishes, while the actual zero rows give the leading
cusp-equivalence indicator with the original half and both signs. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspHeightProfile_high_cusp (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ∀ t≤1, f t=0) (x y : ℝ) (hy : 1≤y) :
    gamma0CuspHeightProfile N a f
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y (zero_lt_one.trans_le hy) x)=
      gamma0CuspEisensteinIndicator N r a*f y := by
  classical
  let p := cuspEisensteinTargetPoint N r y (zero_lt_one.trans_le hy) x
  let S : Set (Gamma0CuspEisensteinRows N r a) := {v | v.val 0=0}
  let ρ (v : Gamma0CuspEisensteinRows N r a) := f (cuspEisensteinNormalizedHeight N r a v p)
  have hi : S.indicator ρ=ρ := by
    funext v
    by_cases hv : v∈S
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact (hf _ (cuspEisensteinNormalizedHeight_nonzero_row_le_one N r a v hv x y hy)).symm
  have he := finsum_set_coe_eq_finsum_mem (f := ρ) S
  rw [finsum_mem_def,hi] at he
  rw [gamma0CuspHeightProfile_target]
  change (1/2:ℂ)*(∑ᶠ v : Gamma0CuspEisensteinRows N r a,ρ v)=_
  rw [← he]
  change (1/2:ℂ)*(∑ᶠ v : CuspEisensteinZeroRows N r a,ρ v.val)=_
  have hz (v : CuspEisensteinZeroRows N r a) : ρ v.val=f y := by
    dsimp only [ρ,p]
    rw [cuspEisensteinNormalizedHeight_zero_row N r a v x y]
  simp_rw [hz]
  rw [finsum_eq_sum_of_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,cuspEisensteinZeroRows_card]
  by_cases h : gamma0EisensteinCuspsEquivalent N r a <;>
    simp [h,gamma0CuspEisensteinIndicator]

theorem gamma0CuspHeightProfile_raw_high (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ∀ t≤1, f t=0) (z : UpperHalfPlane)
    (hz : (gamma0CuspTrueWidth N r:ℝ)≤z.im) :
    gamma0CuspHeightProfile N a f (r⁻¹ • z)=
      gamma0CuspEisensteinIndicator N r a*f (z.im/(gamma0CuspTrueWidth N r:ℝ)) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  let p : UpperHalfPlane := (cuspWidthDilation w hw)⁻¹ • z
  have him : p.im=z.im/w := cuspWidthDilation_im_inv_smul w hw z
  have hp1 : 1≤p.im := by rw [him];exact (one_le_div hw).mpr hz
  have he : gamma0TrueCuspScaling N r • p=r⁻¹ • z := by
    dsimp [p,w]
    rw [gamma0TrueCuspScaling,mul_smul,smul_inv_smul,← map_inv]
    exact atkinRealMap_smul r⁻¹ z
  have hp : gamma0EisensteinHorizontalPoint p.im p.im_pos p.re=p := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> rfl
  have hf' := gamma0CuspHeightProfile_high_cusp N r a f hf p.re p.im hp1
  rw [hp,he,him] at hf'
  exact hf'

theorem gamma0CuspEisensteinCutoff_high_cusp_all_parameters (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (x y : ℝ) (hy : 2≤y) :
    gamma0CuspEisensteinCutoff N a s (gamma0TrueCuspScaling N r •
      gamma0EisensteinHorizontalPoint y (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x)=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s := by
  rw [gamma0CuspEisensteinCutoff_eq_profile,
    gamma0CuspHeightProfile_high_cusp N r a (eisensteinVerticalCutoffMode s)
      (fun _ ht => eisensteinVerticalCutoffMode_zero s ht) x y (by linarith),
    eisensteinVerticalCutoffMode_one s hy]

end ArtinMatthews
