module

public import ArtinMatthews.SpectralEisensteinHeightCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! In every high target cusp the source-height cutoff removes exactly the
actual leading term; every nonzero lower row lies below its support. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinNormalizedHeight_target (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (x y : ℝ) (hy : 0 < y) :
    cuspEisensteinNormalizedHeight N r a v (cuspEisensteinTargetPoint N r y hy x)=
      (((gamma0CuspTrueWidth N r:ℝ)*y)/
        ((((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*x+v.val 1)^2+
          (((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*y)^2))/(gamma0CuspTrueWidth N a:ℝ) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hcoe : ((cuspEisensteinTargetPoint N r y hy x):ℂ)=Complex.mk (w*x) (w*y) := by
    rw [cuspEisensteinTargetPoint,cuspWidthDilation_coe_smul]
    apply Complex.ext <;> simp [w,gamma0EisensteinHorizontalPoint]
  have him : (cuspEisensteinTargetPoint N r y hy x).im=w*y := cuspWidthDilation_im_smul _ _ _
  rw [cuspEisensteinNormalizedHeight,cuspEisensteinRowHeight_row,him,hcoe]
  congr 2
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,w,pow_two]
  ring

theorem cuspEisensteinNormalizedHeight_nonzero_row_le_one (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (hv : v.val 0 ≠ 0)
    (x y : ℝ) (hy : 1 ≤ y) :
    cuspEisensteinNormalizedHeight N r a v
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) x) ≤ 1 := by
  have hw : (1:ℝ) ≤ gamma0CuspTrueWidth N r := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  have ha : (1:ℝ) ≤ gamma0CuspTrueWidth N a := by exact_mod_cast gamma0CuspTrueWidth_pos N a
  have hc : (1:ℝ) ≤ (v.val 0:ℝ)^2 := by
    have hcZ : 1 ≤ v.val 0 ∨ v.val 0 ≤ -1 := by omega
    rcases hcZ with hcZ | hcZ
    · have hcR : (1:ℝ) ≤ v.val 0 := by exact_mod_cast hcZ
      nlinarith
    · have hcR : (v.val 0:ℝ) ≤ -1 := by exact_mod_cast hcZ
      nlinarith
  let b : ℝ := (gamma0CuspTrueWidth N r:ℝ)*y
  have hb : 1 ≤ b := by
    simpa only [one_mul] using mul_le_mul hw hy zero_le_one (le_trans zero_le_one hw)
  have hcB : b^2 ≤ ((v.val 0:ℝ)*b)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg b)]
  let Q := (((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*x+v.val 1)^2+
    (((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*y)^2
  have hQ : b ≤ Q := by
    dsimp [Q]
    have he : ((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*y=(v.val 0:ℝ)*b := by dsimp [b];ring
    rw [he]
    nlinarith [sq_nonneg (((v.val 0:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*x+v.val 1)]
  have hQp : 0 < Q := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hb) hQ
  rw [cuspEisensteinNormalizedHeight_target]
  change (b/Q)/(gamma0CuspTrueWidth N a:ℝ) ≤ 1
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one ha)).mpr
  apply (div_le_iff₀ hQp).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hQp.le]

theorem cuspEisensteinCutoffTerm_nonzero_row_zero (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (v : Gamma0CuspEisensteinRows N r a) (hv : v.val 0 ≠ 0)
    (x y : ℝ) (hy : 1 ≤ y) :
    cuspEisensteinCutoffTerm N r a s v
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) x)=0 := by
  unfold cuspEisensteinCutoffTerm
  rw [eisensteinHeightCutoff_zero (cuspEisensteinNormalizedHeight_nonzero_row_le_one N r a v hv x y hy)]
  simp

theorem cuspEisensteinNormalizedHeight_zero_row (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : CuspEisensteinZeroRows N r a) (x y : ℝ) (hy : 0 < y) :
    cuspEisensteinNormalizedHeight N r a v.val (cuspEisensteinTargetPoint N r y hy x)=y := by
  have hw := gamma0EisensteinCuspsEquivalent_width N r a
    (cuspEisensteinZeroRow_implies_equivalent N r a v)
  have ha : (gamma0CuspTrueWidth N a:ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N a).ne'
  rw [cuspEisensteinNormalizedHeight_target,hw,v.property]
  rcases cuspEisensteinZeroRows_unit N r a v with hd | hd <;> rw [hd] <;> simp [ha]

theorem cuspEisensteinCutoffTerm_zero_row (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (v : CuspEisensteinZeroRows N r a) (x y : ℝ) (hy : 2 ≤ y) :
    cuspEisensteinCutoffTerm N r a s v.val
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x)=(y:ℂ)^s := by
  unfold cuspEisensteinCutoffTerm
  rw [cuspEisensteinNormalizedHeight_zero_row,eisensteinHeightCutoff_one hy]
  simp

end ArtinMatthews
