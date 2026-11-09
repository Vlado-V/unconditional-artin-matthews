module

public import ArtinMatthews.SpectralJForwardInverse
public import ArtinMatthews.SpectralBareModulusSeries


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section

theorem spectralJForwardTransform_bareKernel
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) (hmn : 0 < m * n) {X : ℝ} (hX : 0 < X) :
    spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X =
      (2 / (X : ℂ)) * (f X - spectralJOddSynthesis f X) := by
  have hinv := spectralJForwardTransform_inverse_apply f hf hc hs hX
  have hk : spectralJWeightedSynthesis
      (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) X =
      (X : ℂ) / 2 * spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X := by
    simp only [spectralJWeightedSynthesis, spectralABLBareKernel,
      spectralWeylIntegerSignMultiplier, ite_eq_left hmn]
  rw [hk] at hinv
  have hXc : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  apply mul_left_cancel₀ (show (X : ℂ) / 2 ≠ 0 from div_ne_zero hXc (by norm_num))
  calc
    (X : ℂ) / 2 * spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X =
        f X - spectralJOddSynthesis f X := by linear_combination -hinv
    _ = _ := by field_simp [hXc] <;> ring

theorem gamma0TrueWidthBareFibre_forwardJ
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
    let X := Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|) * (2 / C)
    gamma0TrueWidthBareFibre N r s c m n (spectralJForwardSpectralWeight f) =
      (gamma0TrueWidthKloostermanSum N r s c.val m n / (C : ℂ)) *
        (f X - spectralJOddSynthesis f X) := by
  letI : NeZero c.val := ⟨c.property.ne'⟩
  dsimp only
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  let K := Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hK : 0 < K := Real.sqrt_pos.mpr (mul_pos
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm))
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)))
  have hX : 0 < K * (2 / C) := mul_pos hK (div_pos two_pos hC)
  unfold gamma0TrueWidthBareFibre
  change gamma0TrueWidthKloostermanSum N r s c.val m n *
    ((K / C ^ 2 : ℝ) : ℂ) *
    spectralABLBareKernel (spectralJForwardSpectralWeight f) m n (K * (2 / C)) =
      (gamma0TrueWidthKloostermanSum N r s c.val m n / (C : ℂ)) *
        (f (K * (2 / C)) - spectralJOddSynthesis f (K * (2 / C)))
  rw [spectralJForwardTransform_bareKernel f hf hc hs m n hmn hX]
  have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hKc : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  push_cast
  field_simp [hCc, hKc]
  <;> ring

end
end ArtinMatthews
