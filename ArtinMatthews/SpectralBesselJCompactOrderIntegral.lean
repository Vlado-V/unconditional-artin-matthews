module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselJOrderJoint
public import ArtinMatthews.SpectralCompactHolomorphicIntegral
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact positive-ray J integral is entire in order.
Its derivative retains the original dx/x density. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralBesselJOrderTransform (f : ℝ → ℂ) (ν : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)

private theorem spectral_besselJ_order_integrand_continuousOn (f : ℝ → ℂ) (hf : Continuous f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (fun p : ℂ × ℝ => f p.2*Complex.besselJ p.1 (p.2 : ℂ)/(p.2 : ℂ))
      (univ ×ˢ tsupport f) := by
  have hJ : ContinuousOn (fun p : ℂ × ℝ => Complex.besselJ p.1 (p.2 : ℂ))
      (univ ×ˢ tsupport f) := fun p h =>
    (spectral_besselJ_order_argument_continuousAt p.1 (hp h.2)).continuousWithinAt
  exact ((hf.comp continuous_snd).continuousOn.mul hJ).div
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
    (fun p h => Complex.ofReal_ne_zero.mpr (show 0 < p.2 from hp h.2).ne')

theorem spectralBesselJOrderTransform_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    IntegrableOn (fun x => f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) (Ioi (0 : ℝ)) := by
  have h := (spectral_besselJ_order_integrand_continuousOn f hf hp).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x hx => ⟨mem_univ ν,hx⟩)
  have hi : IntegrableOn (fun x => f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) (tsupport f) :=
    h.integrableOn_compact hc
  have hs : Function.support (fun x => f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) ⊆ tsupport f := by
    intro x hx
    by_contra hx'
    have hf0 := image_eq_zero_of_notMem_tsupport hx'
    exact hx (by simp [hf0])
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp hi).integrableOn

private theorem spectral_compact_supported_div_integral (f g : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ x in Ioi (0 : ℝ), f x*g x/(x : ℂ)) =
      ∫ x in tsupport f, f x*g x/(x : ℂ) := by
  calc
    _ = ∫ x : ℝ, f x*g x/(x : ℂ) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hp h))
        simp [hf0])
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hf0])).symm

theorem spectralBesselJOrderTransform_hasDerivAt (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    HasDerivAt (spectralBesselJOrderTransform f)
      (∫ x in Ioi (0 : ℝ), f x*deriv (fun w => Complex.besselJ w (x : ℂ)) ν/(x : ℂ)) ν := by
  let F (w : ℂ) (x : ℝ) := f x*Complex.besselJ w (x : ℂ)/(x : ℂ)
  have hD (x : ℝ) (hx : x ∈ tsupport f) (w : ℂ) :
      HasDerivAt (fun v => F v x) (f x*deriv (fun v => Complex.besselJ v (x : ℂ)) w/(x : ℂ)) w :=
    (((spectral_besselJ_order_differentiable (hp hx) w).hasDerivAt).const_mul (f x)).div_const _
  have hHol (x : ℝ) (hx : x ∈ tsupport f) : Differentiable ℂ (fun w => F w x) :=
    fun w => (hD x hx w).differentiableAt
  have h := spectral_hasDerivAt_compact_holomorphic_integral hc
    (spectral_besselJ_order_integrand_continuousOn f hf hp) hHol ν
  have hF : spectralBesselJOrderTransform f = fun w => ∫ x in tsupport f, F w x := by
    funext w
    exact spectral_compact_supported_div_integral f (fun x => Complex.besselJ w (x : ℂ)) hp
  rw [hF, spectral_compact_supported_div_integral f _ hp]
  convert h using 1
  apply setIntegral_congr_fun hc.isClosed.measurableSet
  intro x hx
  exact (hD x hx ν).deriv.symm

theorem spectralBesselJOrderTransform_differentiable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Differentiable ℂ (spectralBesselJOrderTransform f) :=
  fun ν => (spectralBesselJOrderTransform_hasDerivAt f hf hc hp ν).differentiableAt

end ArtinMatthews
