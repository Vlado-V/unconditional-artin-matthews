module

public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralEisensteinCutoffAtCusps


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact forcing vanishes above normalized height two in every
actual cusp. All parameters and both central signs are retained. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem eisensteinVerticalCutoffError_zero_closed (s : ℂ) {t : ℝ}
    (ht : t ≤ 1 ∨ 2 ≤ t) : eisensteinVerticalCutoffError s t=0 := by
  have hc : IsClosed {u : ℝ | eisensteinVerticalCutoffError s u=0} :=
    isClosed_eq (eisensteinVerticalCutoffError_smooth s).continuous continuous_const
  rcases ht with ht | ht
  · have he : Iio (1:ℝ) ⊆ {u : ℝ | eisensteinVerticalCutoffError s u=0} :=
      fun u hu => eisensteinVerticalCutoffError_zero s (Or.inl hu)
    have hh := closure_minimal he hc
    rw [closure_Iio] at hh
    exact hh ht
  · have he : Ioi (2:ℝ) ⊆ {u : ℝ | eisensteinVerticalCutoffError s u=0} :=
      fun u hu => eisensteinVerticalCutoffError_zero s (Or.inr hu)
    have hh := closure_minimal he hc
    rw [closure_Ioi] at hh
    exact hh ht

theorem gamma0CuspHeightProfile_target (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a f (gamma0TrueCuspScaling N r • z)=
      (1/2:ℂ)*∑ᶠ v : Gamma0CuspEisensteinRows N r a,
        f (cuspEisensteinNormalizedHeight N r a v
          (cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
            (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z)) := by
  unfold gamma0CuspHeightProfile gamma0TrueCuspScaling
  rw [mul_smul,← map_inv,atkinRealMap_smul]
  congr 1
  have he := finsum_comp_equiv
    (f := fun v : Gamma0CuspEisensteinRows N r a =>
      f (cuspEisensteinNormalizedHeight N r a v
        (cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
          (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z)))
    (gamma0CuspEisensteinRowReindexEquiv N 1 r a)
  simpa only [cuspEisensteinNormalizedHeight,cuspEisensteinRowHeight_reindex,one_mul] using he

theorem gamma0CuspEisensteinCompactForcing_high_cusp (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (x y : ℝ) (hy : 2 ≤ y) :
    gamma0CuspEisensteinCompactForcing N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x)=0 := by
  rw [gamma0CuspEisensteinCompactForcing,gamma0CuspHeightProfile_target]
  have hz (v : Gamma0CuspEisensteinRows N r a) :
      eisensteinVerticalCutoffError s (cuspEisensteinNormalizedHeight N r a v
        (cuspEisensteinTargetPoint N r y
          (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x))=0 := by
    by_cases hv : v.val 0=0
    · have he := cuspEisensteinNormalizedHeight_zero_row N r a ⟨v,hv⟩ x y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy)
      rw [he]
      exact eisensteinVerticalCutoffError_zero_closed s (Or.inr hy)
    · exact eisensteinVerticalCutoffError_zero_closed s (Or.inl
        (cuspEisensteinNormalizedHeight_nonzero_row_le_one N r a v hv x y (by linarith)))
  change (1/2:ℂ)*(∑ᶠ v : Gamma0CuspEisensteinRows N r a,
    eisensteinVerticalCutoffError s (cuspEisensteinNormalizedHeight N r a v
      (cuspEisensteinTargetPoint N r y _ x)))=0
  simp only [hz,finsum_zero,mul_zero]

end ArtinMatthews
