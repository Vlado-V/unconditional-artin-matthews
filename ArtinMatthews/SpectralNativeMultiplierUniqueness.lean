module

public import ArtinMatthews.SpectralAmbientTestPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full ambient resolution determines a vector from its
cuspidal, continuous and residual data. This criterion retains every sector. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0AmbientTestOperator_eq_of_spectral_data (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (v w : Gamma0RegionL2 N)
    (hcusp : ∀ i : Gamma0AllHeightSpectralIndex N,
      inner ℂ (gamma0FullCuspidalSpectralBasis N i).val w =
        gamma0CuspidalTestSymbol N h i*inner ℂ (gamma0FullCuspidalSpectralBasis N i).val v)
    (hcontinuous : gamma0EisensteinAnalysis N w =
      gamma0EisensteinTestMultiplier N h (gamma0EisensteinAnalysis N v))
    (hresidual : ∀ l ∈ gamma0ResidualEnergyWindow N, ∀ j,
      inner ℂ (gamma0ResidualEigenbasis N l j).val w =
        h l*inner ℂ (gamma0ResidualEigenbasis N l j).val v) :
    w = gamma0AmbientTestOperator N h v := by
  apply ext_inner_left ℂ
  intro u
  have hone := gamma0AmbientTestOperator_pair N 1 u w
  rw [gamma0AmbientTestOperator_one] at hone
  change inner ℂ u w = _ at hone
  have hc : (∑' i : Gamma0AllHeightSpectralIndex N, gamma0CuspidalTestSymbol N 1 i*
      (inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val*
        inner ℂ (gamma0FullCuspidalSpectralBasis N i).val w)) =
      ∑' i : Gamma0AllHeightSpectralIndex N, gamma0CuspidalTestSymbol N h i*
        (inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val v) := by
    apply tsum_congr
    intro i
    rw [hcusp i]
    change (1 : ℂ)*(_*(_*_)) = _
    ring
  have hi := gamma0EisensteinTestMultiplier_inner N 1
    (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N w)
  rw [gamma0EisensteinTestMultiplier_one] at hi
  change inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N w) = _ at hi
  have he : (∫ t, spectralContinuousTestSymbol 1 t*
      gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N w) t
        ∂gamma0EisensteinSpectralMeasure) =
      ∫ t, spectralContinuousTestSymbol h t*
        gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N v) t
          ∂gamma0EisensteinSpectralMeasure := by
    rw [← hi,hcontinuous,gamma0EisensteinTestMultiplier_inner]
  have hr : (∑ l ∈ gamma0ResidualEnergyWindow N, (1 : SpectralEnergyTest) l*
      ∑ j, inner ℂ u (gamma0ResidualEigenbasis N l j).val*
        inner ℂ (gamma0ResidualEigenbasis N l j).val w) =
      ∑ l ∈ gamma0ResidualEnergyWindow N, h l*
        ∑ j, inner ℂ u (gamma0ResidualEigenbasis N l j).val*
          inner ℂ (gamma0ResidualEigenbasis N l j).val v := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [hresidual l hl]
    change (1 : ℂ)*_ = _
    rw [one_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc,he,hr] at hone
  exact hone.trans (gamma0AmbientTestOperator_pair N h u v).symm

end ArtinMatthews
