module

public import ArtinMatthews.SpectralPeterssonCutPeriodization
public import ArtinMatthews.SpectralPeterssonCutRadial
public import ArtinMatthews.SpectralPeterssonSeedProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The original sharp-cut seed pairing separates into its exact
horizontal character and vertical Gamma density. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonStripCut_pair_coordinates (k : ℕ) (hk : 2 ≤ k)
    (m n : ℕ+) (A : ℝ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed m A)
      (spectralPeterssonStripCutSeed n A) z =
      (Ioc (0 : ℝ) 1).indicator (fun x => atkinPhase (((n : ℝ)-(m : ℝ))*x)) z.re *
        (z.im^2*spectralPeterssonCutPairRadial k m n A z.im : ℝ) := by
  have hstrip : z ∈ hyperbolicCuspStrip 1 0 ↔ z.re ∈ Ioc (0 : ℝ) 1 := by
    change (z.re ∈ Ioc (0 : ℝ) 1 ∧ 0 < z.im) ↔ _
    simp only [z.im_pos,and_true]
  simp only [UpperHalfPlane.petersson,zpow_natCast]
  by_cases hx : z.re ∈ Ioc (0 : ℝ) 1
  · have hz := hstrip.mpr hx
    simp only [spectralPeterssonStripCutSeed,indicator_of_mem hz,indicator_of_mem hx]
    by_cases hm : A < 4*Real.pi*(m : ℝ)*z.im
    · by_cases hn : A < 4*Real.pi*(n : ℝ)*z.im
      · simp only [spectralPeterssonHeightCutSeed,if_pos hm,if_pos hn]
        rw [spectralHolomorphicCuspSeed_pair]
        rw [spectralPeterssonCutPairRadial,if_pos ⟨hm,hn⟩]
        have hpow : z.im^2*z.im^(k-2) = z.im^k := by
          rw [← pow_add]
          congr 1
          omega
        have hreal : z.im^2*(z.im^(k-2)*Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im))) =
            Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im))*z.im^k := by
          rw [← mul_assoc,hpow]
          ring
        rw [hreal]
        push_cast
        ring
      · simp [spectralPeterssonHeightCutSeed,hm,hn,spectralPeterssonCutPairRadial]
    · simp [spectralPeterssonHeightCutSeed,hm,spectralPeterssonCutPairRadial]
  · have hz : z ∉ hyperbolicCuspStrip 1 0 := fun h => hx (hstrip.mp h)
    simp only [spectralPeterssonStripCutSeed,indicator_of_notMem hz,indicator_of_notMem hx,
      UpperHalfPlane.petersson,map_zero,zero_mul]

end ArtinMatthews
