module

public import ArtinMatthews.SpectralJForwardWeightReality


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual real-valued compact tests associated with a complex source
preserve its support and smoothness. -/
noncomputable section
open Set Complex
open scoped ContDiff ComplexConjugate

namespace ArtinMatthews

def spectralJRealTest (f : ℝ → ℂ) (x : ℝ) : ℂ := ((f x).re : ℂ)
def spectralJImagTest (f : ℝ → ℂ) (x : ℝ) : ℂ := ((f x).im : ℂ)

theorem spectralJRealTest_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (spectralJRealTest f) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf)

theorem spectralJImagTest_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (spectralJImagTest f) :=
  Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf)

theorem spectralJRealTest_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spectralJRealTest f) :=
  Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf)

theorem spectralJImagTest_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spectralJImagTest f) :=
  Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf)

theorem spectralJRealTest_hasCompactSupport (f : ℝ → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (spectralJRealTest f) :=
  hc.comp_left (g := fun z : ℂ => (z.re : ℂ)) (by simp)

theorem spectralJImagTest_hasCompactSupport (f : ℝ → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (spectralJImagTest f) :=
  hc.comp_left (g := fun z : ℂ => (z.im : ℂ)) (by simp)

theorem spectralJRealTest_tsupport (f : ℝ → ℂ) :
    tsupport (spectralJRealTest f) ⊆ tsupport f :=
  tsupport_comp_subset (g := fun z : ℂ => (z.re : ℂ)) (by simp) f

theorem spectralJImagTest_tsupport (f : ℝ → ℂ) :
    tsupport (spectralJImagTest f) ⊆ tsupport f :=
  tsupport_comp_subset (g := fun z : ℂ => (z.im : ℂ)) (by simp) f

theorem spectralJRealTest_conj (f : ℝ → ℂ) (x : ℝ) :
    conj (spectralJRealTest f x) = spectralJRealTest f x := by
  simp [spectralJRealTest]

theorem spectralJImagTest_conj (f : ℝ → ℂ) (x : ℝ) :
    conj (spectralJImagTest f x) = spectralJImagTest f x := by
  simp [spectralJImagTest]

theorem spectralJTest_parts (f : ℝ → ℂ) :
    f = spectralJRealTest f + fun x => I*spectralJImagTest f x := by
  funext x
  simpa only [Pi.add_apply,spectralJRealTest,spectralJImagTest,mul_comm] using (Complex.re_add_im (f x)).symm

end ArtinMatthews
