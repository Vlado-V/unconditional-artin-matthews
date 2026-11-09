module

public import ArtinMatthews.SpectralCuspLocalSmoothExtension
public import ArtinMatthews.SpectralCuspFourierLocalTools
public import ArtinMatthews.SpectralCuspTwoCellFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical Fourier integral over the interior period [N/2,3N/2].
Only smoothness on the open two-cell strip is used. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace ArtinMatthews

def cuspInteriorFourierCoefficient (N : ℝ) (n : ℤ) (u : ℝ × ℝ → ℂ) : ℝ → ℂ :=
  fun y => cuspFourierPhase N n (N / 2) *
    cuspHorizontalWeightedMean N (cuspFourierPhase N n)
      (fun p => u (p.1 + N / 2, p.2)) y

theorem cuspInteriorFourierCoefficient_germ (N Y y₀ : ℝ) (_hN : 0 < N) (hy₀ : Y < y₀)
    (u G : ℝ × ℝ → ℂ)
    (he : ∀ y, |y - y₀| < (y₀ - Y) / 4 → ∀ x ∈ Icc (N / 2) (3 * N / 2),
      G =ᶠ[𝓝 (x, y)] u) :
    cuspInteriorFourierCoefficient N n G =ᶠ[𝓝 y₀] cuspInteriorFourierCoefficient N n u := by
  filter_upwards [Metric.ball_mem_nhds y₀ (by linarith : 0 < (y₀ - Y) / 4)] with y hy
  change dist y y₀ < (y₀ - Y) / 4 at hy
  rw [Real.dist_eq] at hy
  unfold cuspInteriorFourierCoefficient cuspHorizontalWeightedMean cuspHorizontalMean
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxp : x + N / 2 ∈ Icc (N / 2) (3 * N / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  dsimp only
  rw [(he y hy (x + N / 2) hxp).eq_of_nhds]

theorem cuspInteriorFourierCoefficient_hasDerivAt (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y))
    (y : ℝ) (hy : Y < y) :
    HasDerivAt (cuspInteriorFourierCoefficient N n u)
      (deriv (cuspInteriorFourierCoefficient N n u) y) y := by
  obtain ⟨G,hG,he⟩ := spectralLocalTwoCell_smooth_extension_uniform N Y y hN hy u hu
  have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G (p.1 + N / 2, p.2)) :=
    hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  have hd := (cuspHorizontalWeightedMean_hasDerivAt N (cuspFourierPhase_contDiff N n) hg
    (hY.trans_lt hy)).const_mul (cuspFourierPhase N n (N / 2))
  have hc := hd.congr_of_eventuallyEq (cuspInteriorFourierCoefficient_germ N Y y hN hy u G he).symm
  rw [← hc.deriv] at hc
  exact hc

theorem cuspInteriorFourierCoefficient_deriv_hasDerivAt (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y))
    (y : ℝ) (hy : Y < y) :
    HasDerivAt (deriv (cuspInteriorFourierCoefficient N n u))
      (deriv (deriv (cuspInteriorFourierCoefficient N n u)) y) y := by
  obtain ⟨G,hG,he⟩ := spectralLocalTwoCell_smooth_extension_uniform N Y y hN hy u hu
  have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G (p.1 + N / 2, p.2)) :=
    hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  have hd := (cuspHorizontalWeightedMean_deriv_hasDerivAt N (cuspFourierPhase N n)
    (cuspFourierPhase_contDiff N n) _ hg y (hY.trans_lt hy)).const_mul
      (cuspFourierPhase N n (N / 2))
  have hglobal : HasDerivAt (deriv (cuspInteriorFourierCoefficient N n G))
      (cuspFourierPhase N n (N / 2) *
        cuspHorizontalWeightedMean N (cuspFourierPhase N n)
          (spectralPlaneSecond (fun p => G (p.1 + N / 2, p.2)) 1) y) y := by
    unfold cuspInteriorFourierCoefficient
    rw [deriv_const_mul_field']
    exact hd
  have hc := hglobal.congr_of_eventuallyEq
    (cuspInteriorFourierCoefficient_germ N Y y hN hy u G he).symm.deriv
  rw [← hc.deriv] at hc
  exact hc

theorem cuspInteriorFourierCoefficient_continuousOn (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y)) :
    ContinuousOn (cuspInteriorFourierCoefficient N n u) (Ioi Y) :=
  fun y hy => (cuspInteriorFourierCoefficient_hasDerivAt N Y hN hY n u hu y hy).continuousAt.continuousWithinAt

theorem cuspInteriorFourierCoefficient_deriv_continuousOn (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y)) :
    ContinuousOn (deriv (cuspInteriorFourierCoefficient N n u)) (Ioi Y) :=
  fun y hy => (cuspInteriorFourierCoefficient_deriv_hasDerivAt N Y hN hY n u hu y hy).continuousAt.continuousWithinAt

end ArtinMatthews
