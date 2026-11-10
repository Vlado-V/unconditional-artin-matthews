module

public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.Metrizable.Urysohn


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine compact smooth plane test supported in positive height defines
an actual compact smooth hyperbolic seed. The support and smoothness are
proved through the actual coordinate inverse, with no extension premise. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported

namespace ArtinMatthews

theorem spectralPlaneTest_hyperbolic_compact (φ : ℝ × ℝ → ℂ)
    (hc : HasCompactSupport φ) (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    HasCompactSupport (fun z : UpperHalfPlane => φ (z.re,z.im)) := by
  let T : ℝ × ℝ → UpperHalfPlane := fun p => UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  have hT : ContinuousOn T {p : ℝ × ℝ | 0 < p.2} := by
    intro p hp
    have him : 0 < (Complex.equivRealProdCLM.symm p).im := by
      simpa only [Complex.equivRealProdCLM_symm_apply,Complex.add_im,Complex.ofReal_im,
        Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
        zero_add,add_zero,Set.mem_ofPred_eq] using hp
    exact (((UpperHalfPlane.contMDiffAt_ofComplex (n := 0) him).continuousAt).comp
      Complex.equivRealProdCLM.symm.continuousAt).continuousWithinAt
  have hK : IsCompact (T '' tsupport φ) := hc.image_of_continuousOn (hT.mono hpositive)
  have hs : Function.support (fun z : UpperHalfPlane => φ (z.re,z.im)) ⊆ T '' tsupport φ := by
    intro z hz
    refine ⟨(z.re,z.im),subset_tsupport φ hz,?_⟩
    change UpperHalfPlane.ofComplex
      (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (z : ℂ))) = z
    rw [Complex.equivRealProdCLM.symm_apply_apply,UpperHalfPlane.ofComplex_apply]
  exact hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hs hK.isClosed)

theorem spectralPlaneTest_hyperbolic_smooth (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => φ ((UpperHalfPlane.ofComplex w).re,(UpperHalfPlane.ofComplex w).im))
      {w : ℂ | 0 < w.im} := by
  apply (hφ.comp Complex.equivRealProdCLM.contDiff).contDiffOn.congr
  intro w hw
  simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hw,UpperHalfPlane.mk_re,
    UpperHalfPlane.mk_im,Complex.equivRealProdCLM_apply,Function.comp_apply]

def h2SmoothSeedOfPlane (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    h2SmoothCompactSeeds :=
  ⟨{ toFun := fun z => φ (z.re,z.im)
     continuous_toFun := hφ.continuous.comp
       (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
     hasCompactSupport' := spectralPlaneTest_hyperbolic_compact φ hc hpositive },
    spectralPlaneTest_hyperbolic_smooth φ hφ⟩

theorem h2SmoothSeedOfPlane_apply (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2})
    (z : UpperHalfPlane) : (h2SmoothSeedOfPlane φ hφ hc hpositive).val z = φ (z.re,z.im) := rfl

theorem h2SmoothSeedOfPlane_support (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    tsupport (h2SmoothSeedOfPlane φ hφ hc hpositive).val ⊆
      (fun z : UpperHalfPlane => (z.re,z.im)) ⁻¹' tsupport φ := by
  apply closure_minimal _ ((isClosed_tsupport φ).preimage
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im))
  intro z hz
  exact subset_tsupport φ hz

end ArtinMatthews
