module

public import ArtinMatthews.SpectralAmbientTestPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar normalization of the actual full ambient multiplier. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0AmbientTestOperator_smul (N : ℕ) [NeZero N]
    (c : ℂ) (h : SpectralEnergyTest) (v : Gamma0RegionL2 N) :
    gamma0AmbientTestOperator N (c • h) v = c • gamma0AmbientTestOperator N h v := by
  apply ext_inner_left ℂ
  intro u
  rw [inner_smul_right,gamma0AmbientTestOperator_pair,gamma0AmbientTestOperator_pair,
    mul_add,mul_add]
  congr 1
  · rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    change (c*gamma0CuspidalTestSymbol N h i)*_ = c*(gamma0CuspidalTestSymbol N h i*_)
    ring
  · congr 1
    · rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      change (c*spectralContinuousTestSymbol h t)*_ = c*(spectralContinuousTestSymbol h t*_)
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      change (c*h l)*_ = c*(h l*_)
      ring

end ArtinMatthews
