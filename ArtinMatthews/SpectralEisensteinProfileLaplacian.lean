module

public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralEisensteinProfileGradient
public import ArtinMatthews.SpectralEisensteinProfileGradientSum
public import ArtinMatthews.SpectralPlaneLaplacianLinearity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal hyperbolic Laplacians of locally finite normalized height profiles. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem spectralSectionPlane_C2_of_smooth (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}) :
    ContDiffOn ℝ 2 (spectralSectionPlane F) {p : ℝ×ℝ | 0 < p.2} := by
  exact (hF.of_le (by simp)).comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn
    (fun p hp => by
      change 0 < p.2 at hp
      change 0 < (Complex.equivRealProdCLM.symm p).im
      simpa only [Complex.equivRealProdCLM_symm_apply,Complex.add_im,
      Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,
      mul_one,mul_zero,zero_mul,add_zero,zero_add] using hp)

theorem h2SectionPositiveLaplacian_congr_of_eventuallyEq (F G : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) (h : F =ᶠ[𝓝 z] G) :
    h2SectionPositiveLaplacian F z=h2SectionPositiveLaplacian G z := by
  have hc : ContinuousAt (fun p : ℝ×ℝ => UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p))
      (z.re,z.im) := by
    have hi : 0 < (Complex.equivRealProdCLM.symm (z.re,z.im)).im := by
      simpa only [Complex.equivRealProdCLM_symm_apply,Complex.add_im,Complex.ofReal_im,
        Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
        zero_mul,add_zero,zero_add] using z.im_pos
    exact ((UpperHalfPlane.contMDiffAt_ofComplex (n := 0) hi).continuousAt).comp
      Complex.equivRealProdCLM.symm.continuousAt
  have hv : UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm (z.re,z.im))=z := by
    rw [show Complex.equivRealProdCLM.symm (z.re,z.im)=(z:ℂ) from
      Complex.equivRealProdCLM.symm_apply_apply (z:ℂ),UpperHalfPlane.ofComplex_apply]
  have he := h.comp_tendsto (hv ▸ hc.tendsto)
  exact spectralPlanePositiveHyperbolic_congr_of_eventuallyEq _ _ he

theorem h2SectionPositiveLaplacian_zero (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (fun _ => (0:ℂ)) z=0 := by
  change spectralPlanePositiveHyperbolic (fun _ => (0:ℂ)) (z.re,z.im)=0
  simp [spectralPlanePositiveHyperbolic,spectralPlanePositiveSecond,spectralPlaneSecond]

theorem h2SectionPositiveLaplacian_finset_sum {ι : Type*} (T : Finset ι)
    (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (fun w : ℂ => F i (UpperHalfPlane.ofComplex w)) {w | 0 < w.im})
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (fun w => ∑ i ∈ T, F i w) z=
      ∑ i ∈ T, h2SectionPositiveLaplacian (F i) z := by
  exact spectralPlanePositiveHyperbolic_finset_sum T (fun i => spectralSectionPlane (F i))
    (fun i _ => spectralSectionPlane_C2_of_smooth (F i) (hF i)) _ z.im_pos

theorem h2SectionPositiveLaplacian_smul (c : ℂ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) {w | 0 < w.im})
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (c • F) z=c*h2SectionPositiveLaplacian F z :=
  spectralPlanePositiveHyperbolic_smul c (spectralSectionPlane F)
    (spectralSectionPlane_C2_of_smooth F hF) _ z.im_pos

theorem cuspEisensteinProfileTerm_laplacian (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (v : Gamma0CuspEisensteinRows N r a)
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (cuspEisensteinProfileTerm N r a f v) z=
      -((cuspEisensteinNormalizedHeight N r a v z:ℂ)^2)*
        deriv (deriv f) (cuspEisensteinNormalizedHeight N r a v z) := by
  let F := eisensteinHeightProfilePlane (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) f
  have hrep (w : UpperHalfPlane) : F (w.re,w.im)=cuspEisensteinProfileTerm N r a f v w := by
    convert cuspEisensteinProfileTerm_plane N r a f v (w.re,w.im) w.im_pos using 1
    congr 1
  have hF : ContDiffOn ℝ 2 F {p : ℝ×ℝ | 0 < p.2} := by
    apply (spectralSectionPlane_C2_of_smooth _ (cuspEisensteinProfileTerm_smooth N r a f hf v)).congr
    intro p hp
    change 0 < p.2 at hp
    have he := cuspEisensteinProfileTerm_plane N r a f v p hp
    have hc : UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)=⟨Complex.mk p.1 p.2,hp⟩ := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (Complex.equivRealProdCLM.symm p).im by
        simpa only [Complex.equivRealProdCLM_symm_apply,Complex.add_im,Complex.ofReal_im,
          Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
          zero_mul,add_zero,zero_add] using hp)]
      congr 1
    exact he.trans (congrArg _ hc.symm)
  have hd := (((hF (z.re,z.im) z.im_pos).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)).fderiv_right
    (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [h2SectionPositiveLaplacian_representation _ F hrep,
    spectralPlanePositiveHyperbolic_eq_hessian _ _ hd,
    eisensteinHeightProfile_hyperbolic_pde _ _ _ (cuspEisensteinRow_coefficients_ne_zero N r a v)
      f hf _ z.im_pos]
  have hh := eisensteinNormalizedRowHeight_eq (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1)
    (cuspEisensteinRow_coefficients_ne_zero N r a v) (z.re,z.im) z.im_pos
  have hh' := cuspEisensteinNormalizedHeightPlane_eq N r a v (z.re,z.im) z.im_pos
  have hH : eisensteinNormalizedRowHeight (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) (z.re,z.im)=
      cuspEisensteinNormalizedHeight N r a v z := by
    convert hh.trans hh' using 1
    congr 1
  rw [hH]

theorem gamma0CuspHeightProfile_laplacian_error (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hlow : ∀ t ≤ ε, f t=0) (eig : ℂ) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (gamma0CuspHeightProfile N a f) z-
      eig*gamma0CuspHeightProfile N a f z=
        gamma0CuspHeightProfile N a (fun h => -((h:ℂ)^2)*deriv (deriv f) h-eig*f h) z := by
  classical
  obtain ⟨T,he,hzero⟩ := gamma0CuspHeightProfile_local_sum_zero N a f hε hlow z
  have hs : ContDiffOn ℝ ∞
      (fun w : ℂ => ∑ v ∈ T, cuspEisensteinProfileTerm N 1 a f v (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} :=
    ContDiffOn.sum (fun v _ => cuspEisensteinProfileTerm_smooth N 1 a f hf v)
  have hz0 (v) (hv : v ∉ T) :
      -((cuspEisensteinNormalizedHeight N 1 a v z:ℂ)^2)*
        deriv (deriv f) (cuspEisensteinNormalizedHeight N 1 a v z)-
          eig*f (cuspEisensteinNormalizedHeight N 1 a v z)=0 := by
    rw [← cuspEisensteinProfileTerm_laplacian N 1 a f hf v z,
      h2SectionPositiveLaplacian_congr_of_eventuallyEq _ _ z (hzero v hv),
      h2SectionPositiveLaplacian_zero]
    have hv0 := (hzero v hv).eq_of_nhds
    change f (cuspEisensteinNormalizedHeight N 1 a v z)=0 at hv0
    rw [hv0]
    ring
  have hR : gamma0CuspHeightProfile N a (fun h => -((h:ℂ)^2)*deriv (deriv f) h-eig*f h) z=
      (1/2:ℂ)*∑ v ∈ T, (-((cuspEisensteinNormalizedHeight N 1 a v z:ℂ)^2)*
        deriv (deriv f) (cuspEisensteinNormalizedHeight N 1 a v z)-
          eig*f (cuspEisensteinNormalizedHeight N 1 a v z)) := by
    unfold gamma0CuspHeightProfile
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    exact hv (hz0 v hn)
  rw [hR,h2SectionPositiveLaplacian_congr_of_eventuallyEq _ _ z he]
  change h2SectionPositiveLaplacian ((1/2:ℂ) •
    (fun w => ∑ v ∈ T, cuspEisensteinProfileTerm N 1 a f v w)) z-
      eig*gamma0CuspHeightProfile N a f z=_
  rw [h2SectionPositiveLaplacian_smul _ _ hs,
    h2SectionPositiveLaplacian_finset_sum T _ (fun v => cuspEisensteinProfileTerm_smooth N 1 a f hf v),
    he.eq_of_nhds]
  simp_rw [cuspEisensteinProfileTerm_laplacian N 1 a f hf]
  rw [Finset.sum_sub_distrib,Finset.mul_sum]
  simp only [← Finset.mul_sum,cuspEisensteinProfileTerm]
  ring

end ArtinMatthews
