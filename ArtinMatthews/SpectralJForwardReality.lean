module

public import ArtinMatthews.SpectralBesselJOrderConjugation
public import ArtinMatthews.SpectralJForwardRealWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Real tests give real values of the actual forward J transform on both
spectral axes. The value at zero follows by the proved removable continuation. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ComplexConjugate

namespace ArtinMatthews

theorem spectralBesselJOrderTransform_conj (f : ℝ → ℂ)
    (hReal : ∀ x : ℝ, conj (f x) = f x) (ν : ℂ) :
    conj (spectralBesselJOrderTransform f ν) =
      spectralBesselJOrderTransform f (conj ν) := by
  unfold spectralBesselJOrderTransform
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change conj (f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) =
    f x*Complex.besselJ (conj ν) (x : ℂ)/(x : ℂ)
  rw [map_div₀,map_mul,hReal,spectral_besselJ_order_conj_positive ν hx,Complex.conj_ofReal]

private theorem spectralJForwardTransform_conj_off_zero (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) {z : ℂ} (hz : z ≠ 0) :
    conj (spectralJForwardTransform f z) = spectralJForwardTransform f (conj z) := by
  have hzc : conj z ≠ 0 := by
    intro he
    have h := congrArg conj he
    exact hz (by simpa using h)
  have hm : conj (-2*I*z) = 2*I*conj z := by simp only [map_mul,map_neg,map_ofNat,Complex.conj_I]; ring
  have hplus : conj (2*I*z) = -2*I*conj z := by simp only [map_mul,map_ofNat,Complex.conj_I]; ring
  have hS : conj (2*Complex.sin ((Real.pi : ℂ)*I*z)) =
      -(2*Complex.sin ((Real.pi : ℂ)*I*conj z)) := by
    rw [map_mul,map_ofNat,← Complex.sin_conj,
      show conj ((Real.pi : ℂ)*I*z) = -((Real.pi : ℂ)*I*conj z) by
        simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]; ring,
      Complex.sin_neg,mul_neg]
  rw [spectralJForwardTransform_eq_divided_order f hf hc hp z,
    spectralJForwardTransform_eq_divided_order f hf hc hp (conj z),
    ite_eq_right hz,ite_eq_right hzc,map_div₀,map_sub,
    spectralBesselJOrderTransform_conj f hReal (-2*I*z),
    spectralBesselJOrderTransform_conj f hReal (2*I*z),hm,hplus,hS,
    div_neg,← neg_div,neg_sub]

theorem spectralJForwardTransform_conj (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (z : ℂ) :
    conj (spectralJForwardTransform f z) = spectralJForwardTransform f (conj z) := by
  by_cases hz : z = 0
  · subst z
    have hB : ContinuousAt (spectralJForwardTransform f) (0 : ℂ) :=
      (spectralJForwardTransform_analyticOnNhd f hf hc hp 0 (by simp)).continuousAt
    have hC : ContinuousAt (fun w : ℂ => conj w) (spectralJForwardTransform f 0) :=
      Complex.continuous_conj.continuousAt
    have hC₀ : ContinuousAt (fun w : ℂ => conj w) (0 : ℂ) := Complex.continuous_conj.continuousAt
    have h₁ : ContinuousAt (fun w : ℂ => conj (spectralJForwardTransform f w)) 0 := hC.comp_of_eq hB rfl
    have h₂ : ContinuousAt (fun w : ℂ => spectralJForwardTransform f (conj w)) 0 :=
      hB.comp_of_eq hC₀ (by simp)
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] (0 : ℂ))
      (h₁.tendsto.mono_left nhdsWithin_le_nhds) (h₂.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact spectralJForwardTransform_conj_off_zero f hf hc hp hReal
      (by simpa only [mem_compl_iff,mem_singleton_iff] using hw)
  · exact spectralJForwardTransform_conj_off_zero f hf hc hp hReal hz

theorem spectralJForwardTransform_real_im_eq_zero (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (t : ℝ) :
    (spectralJForwardTransform f (t : ℂ)).im = 0 := by
  have h := congrArg Complex.im (spectralJForwardTransform_conj f hf hc hp hReal (t : ℂ))
  simp only [Complex.conj_im,Complex.conj_ofReal] at h
  linarith

theorem spectralJForwardTransform_imaginary_im_eq_zero (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (κ : ℝ) :
    (spectralJForwardTransform f ((κ : ℂ)*I)).im = 0 := by
  have h := spectralJForwardTransform_conj f hf hc hp hReal ((κ : ℂ)*I)
  rw [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,
    spectralJForwardTransform_even f] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

end ArtinMatthews
