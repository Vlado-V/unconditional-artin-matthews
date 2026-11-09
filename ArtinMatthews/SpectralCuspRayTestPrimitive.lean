module

public import ArtinMatthews.SpectralPositiveTestPrimitive


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact primitives of zero-mean tests within a positive cusp tail. -/
namespace ArtinMatthews.SpectralCuspRayRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {Y : ℝ}

theorem rayTest_support_enclosure (σ : ℝ → ℝ)
    (hcompact : HasCompactSupport σ) (hsupport : tsupport σ ⊆ Ioi Y) :
    ∃ a b : ℝ, Y<a ∧ a<Y+1 ∧ Y+1<b ∧ tsupport σ ⊆ Ioo a b := by
  by_cases hne : (tsupport σ).Nonempty
  · obtain ⟨c,hc⟩ := hcompact.exists_isLeast hne
    obtain ⟨d,hd⟩ := hcompact.exists_isGreatest hne
    have hcY : Y<c := hsupport hc.1
    refine ⟨(Y+min c (Y+1))/2,max d (Y+1)+1,?_,?_,?_,?_⟩
    · have := lt_min hcY (by linarith : Y<Y+1)
      linarith
    · have := min_le_right c (Y+1)
      linarith
    · have := le_max_right d (Y+1)
      linarith
    · intro x hx
      have hcx := hc.2 hx
      have hxd := hd.2 hx
      have hmin := min_le_left c (Y+1)
      have hmax := le_max_left d (Y+1)
      constructor <;> linarith
  · refine ⟨Y+1/2,Y+2,by linarith,by linarith,by linarith,?_⟩
    exact fun x hx => (hne ⟨x,hx⟩).elim

theorem rayTestPrimitive_exists (hY : 0 ≤ Y) (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hcompact : HasCompactSupport σ) (hsupport : tsupport σ ⊆ Ioi Y)
    (hmean : ∫ t, σ t=0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioi Y ∧ deriv ρ=σ := by
  obtain ⟨a,b,ha,_,_,hs⟩ := rayTest_support_enclosure σ hcompact hsupport
  have hp := spectralPositiveTestPrimitive_tsupport (lt_of_le_of_lt hY ha) hs hmean
  exact ⟨spectralPositiveTestPrimitive σ,spectralPositiveTestPrimitive_contDiff hσ,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hp,
    fun _ hx => ha.trans_le (hp hx).1,spectralPositiveTestPrimitive_deriv hσ.continuous⟩

end
end ArtinMatthews.SpectralCuspRayRegularity
